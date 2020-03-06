'''
@Author: Guojun Tang
@Date: 2020-02-22 03:20:20
@LastEditTime: 2020-03-06 15:35:44
@LastEditors: Please set LastEditors
@Description:  sm4_dfa for python
@FilePath: \sm4\sm4.py

reference:
sm4: https://github.com/duanhongyi/gmssl/blob/master/gmssl
dfa: https://github.com/SideChannelMarvels/JeanGrey/blob/master/phoenixAES/
'''
import random
from enum import Enum

FaultStatus = Enum('FaultStatus', 'Crash Loop NoFault MinorFault MajorFault WrongFault round31Fault round30Fault round29Fault')


blockSize = 16
sliceSize = blockSize // 4

xor = lambda a, b:list(map(lambda x, y: x ^ y, a, b))

rotl = lambda x, n:((x << n) & 0xffffffff) | ((x >> (32 - n)) & 0xffffffff)

get_uint32_be = lambda key_data:((key_data[0] << 24) | (key_data[1] << 16) | (key_data[2] << 8) | (key_data[3]))

get_uint32_le = lambda key_data:((key_data[3] << 24) | (key_data[2] << 16) | (key_data[1] << 8) | (key_data[0]))

put_uint32_be = lambda n:[((n>>24)&0xff), ((n>>16)&0xff), ((n>>8)&0xff), ((n)&0xff)]

bytes_to_list = lambda data: [i for i in data]

list_to_bytes = lambda data: b''.join([bytes((i,)) for i in data])

dump_byte = lambda a:print(''.join(map(lambda x:('/x' if len(hex(x))>=4 else '/x0')+hex(x)[2:],a)))

l_inv = lambda c: c ^ rotl(c, 2) ^ rotl(c, 4) ^ rotl(c, 8) ^ rotl(c, 12) ^ rotl(c, 14) ^ rotl(c, 16) ^ rotl(c, 18) ^ rotl(c, 22) ^ rotl(c, 24) ^ rotl(c, 30)

int2bytes = lambda state, size: (state).to_bytes(size, byteorder = 'big', signed = False)

bytes2int = lambda state: int.from_bytes(state, 'big', signed=False)

intersect = lambda a,b: [val for val in a if val in b]

singleState = lambda a, index: (a >> (index * 8)) &  0xff

getSlices = lambda block:[(block >> (32 * i) & 0xffffffff )for i in range(0,4)]

byte2slices = lambda state:[get_uint32_be(state[i * 4 : (i + 1) * 4 ]) for i in range(4)]

find_candidate_index = lambda diff: [i  for i in range(4, len(diff)) if diff[i] is not b'\x00'][0] % 4

def check_diff(diffmap, n):
    for i in range(n-1):
        if diffmap[i] is not i:
            return False
    return True
SM4_ENCRYPT = 0
SM4_DECRYPT = 1


SM4_BOXES_TABLE = [
    0xd6,0x90,0xe9,0xfe,0xcc,0xe1,0x3d,0xb7,0x16,0xb6,0x14,0xc2,0x28,0xfb,0x2c,
    0x05,0x2b,0x67,0x9a,0x76,0x2a,0xbe,0x04,0xc3,0xaa,0x44,0x13,0x26,0x49,0x86,
    0x06,0x99,0x9c,0x42,0x50,0xf4,0x91,0xef,0x98,0x7a,0x33,0x54,0x0b,0x43,0xed,
    0xcf,0xac,0x62,0xe4,0xb3,0x1c,0xa9,0xc9,0x08,0xe8,0x95,0x80,0xdf,0x94,0xfa,
    0x75,0x8f,0x3f,0xa6,0x47,0x07,0xa7,0xfc,0xf3,0x73,0x17,0xba,0x83,0x59,0x3c,
    0x19,0xe6,0x85,0x4f,0xa8,0x68,0x6b,0x81,0xb2,0x71,0x64,0xda,0x8b,0xf8,0xeb,
    0x0f,0x4b,0x70,0x56,0x9d,0x35,0x1e,0x24,0x0e,0x5e,0x63,0x58,0xd1,0xa2,0x25,
    0x22,0x7c,0x3b,0x01,0x21,0x78,0x87,0xd4,0x00,0x46,0x57,0x9f,0xd3,0x27,0x52,
    0x4c,0x36,0x02,0xe7,0xa0,0xc4,0xc8,0x9e,0xea,0xbf,0x8a,0xd2,0x40,0xc7,0x38,
    0xb5,0xa3,0xf7,0xf2,0xce,0xf9,0x61,0x15,0xa1,0xe0,0xae,0x5d,0xa4,0x9b,0x34,
    0x1a,0x55,0xad,0x93,0x32,0x30,0xf5,0x8c,0xb1,0xe3,0x1d,0xf6,0xe2,0x2e,0x82,
    0x66,0xca,0x60,0xc0,0x29,0x23,0xab,0x0d,0x53,0x4e,0x6f,0xd5,0xdb,0x37,0x45,
    0xde,0xfd,0x8e,0x2f,0x03,0xff,0x6a,0x72,0x6d,0x6c,0x5b,0x51,0x8d,0x1b,0xaf,
    0x92,0xbb,0xdd,0xbc,0x7f,0x11,0xd9,0x5c,0x41,0x1f,0x10,0x5a,0xd8,0x0a,0xc1,
    0x31,0x88,0xa5,0xcd,0x7b,0xbd,0x2d,0x74,0xd0,0x12,0xb8,0xe5,0xb4,0xb0,0x89,
    0x69,0x97,0x4a,0x0c,0x96,0x77,0x7e,0x65,0xb9,0xf1,0x09,0xc5,0x6e,0xc6,0x84,
    0x18,0xf0,0x7d,0xec,0x3a,0xdc,0x4d,0x20,0x79,0xee,0x5f,0x3e,0xd7,0xcb,0x39,
    0x48,
]

# System parameter
SM4_FK = [0xa3b1bac6,0x56aa3350,0x677d9197,0xb27022dc]

# fixed parameter
SM4_CK = [
    0x00070e15,0x1c232a31,0x383f464d,0x545b6269,
    0x70777e85,0x8c939aa1,0xa8afb6bd,0xc4cbd2d9,
    0xe0e7eef5,0xfc030a11,0x181f262d,0x343b4249,
    0x50575e65,0x6c737a81,0x888f969d,0xa4abb2b9,
    0xc0c7ced5,0xdce3eaf1,0xf8ff060d,0x141b2229,
    0x30373e45,0x4c535a61,0x686f767d,0x848b9299,
    0xa0a7aeb5,0xbcc3cad1,0xd8dfe6ed,0xf4fb0209,
    0x10171e25,0x2c333a41,0x484f565d,0x646b7279
]
def gen_IN_table():
    #Find {x: S(x) ^ S(x ^ diff_in) = diff_out } for all diff_in and diff_out
    IN_table = [[[] for i in range(2 ** 8)]for j in range(2 ** 8)]
    for diff_in in range(1,2 ** 8):
        for x in range(2 ** 8):
            diff_out = SM4_BOXES_TABLE[x] ^ SM4_BOXES_TABLE[diff_in ^ x]
            IN_table[diff_in][diff_out].append(x)
    return IN_table

def recovery_key(last_round_key):
    """
    last_round_key = [k31, k30, k29, k28] as input
    """
    rk = [0] * 36
    rk[32:] = last_round_key[::-1]
    for i in range(31, -1, -1):
       rk[i] = rk[i + 4] ^ round_key(rk[i + 1] ^ rk[i + 2] ^ rk[i + 3] ^ SM4_CK[i])
    rk[:4] = xor(rk[:4], SM4_FK)
    return rk

def get_masterKey(sk):
    MK = b''.join(int2bytes(x, sliceSize)  for x in sk[:4])
    return MK

def round_key(ka):
    b = [0, 0, 0, 0]
    a = put_uint32_be(ka)
    b[0] = SM4_BOXES_TABLE[a[0]]
    b[1] = SM4_BOXES_TABLE[a[1]]
    b[2] = SM4_BOXES_TABLE[a[2]]
    b[3] = SM4_BOXES_TABLE[a[3]]
    bb = get_uint32_be(b[0:4])
    rk = bb ^ (rotl(bb, 13)) ^ (rotl(bb, 23))
    return rk

def set_key(key, mode):
    key = bytes_to_list(key)
    sk = [0] * 32
    MK = [0, 0, 0, 0]
    k = [0]*36
    MK[0:4] = byte2slices(key)
    k[0:4] = xor(MK[0:4], SM4_FK[0:4])
    for i in range(32):
        k[i + 4] = k[i] ^ (
            round_key(k[i + 1] ^ k[i + 2] ^ k[i + 3] ^ SM4_CK[i]))
        sk[i] = k[i + 4]
    mode = mode
    if mode == SM4_DECRYPT:
        for idx in range(16):
            t = sk[idx]
            sk[idx] = sk[31 - idx]
            sk[31 - idx] = t
    return sk


def f_function( x0, x1, x2, x3, rk):
        # "T algorithm" == "L algorithm" + "t algorithm".
        # args:    [in] a: a is a 32 bits unsigned value;
        # return: c: c is calculated with line algorithm "L" and nonline algorithm "t"
    def sm4_l_t(ka):
        b = [0, 0, 0, 0]
        a = put_uint32_be(ka)
        b[0] = SM4_BOXES_TABLE[a[0]]
        b[1] = SM4_BOXES_TABLE[a[1]]
        b[2] = SM4_BOXES_TABLE[a[2]]
        b[3] = SM4_BOXES_TABLE[a[3]]
        bb = get_uint32_be(b[0:4])
        c = bb ^ (rotl(bb, 2)) ^ (rotl(bb, 10)) ^ (rotl(bb, 18)) ^ (rotl(bb, 24))
        return c
    return (x0 ^ sm4_l_t(x1 ^ x2 ^ x3 ^ rk))

def round(sk, in_put):
    out_put = []
    ulbuf = [0]*36
    ulbuf[0:4] = byte2slices(in_put)
    for idx in range(32):
        ulbuf[idx + 4] = f_function(ulbuf[idx], ulbuf[idx + 1], ulbuf[idx + 2], ulbuf[idx + 3], sk[idx])
    out_put += put_uint32_be(ulbuf[35])
    out_put += put_uint32_be(ulbuf[34])
    out_put += put_uint32_be(ulbuf[33])
    out_put += put_uint32_be(ulbuf[32])
    return out_put

def sm4_encrypt(in_put, sk):
    in_put = bytes_to_list(in_put)
    output = round(sk, in_put)
    return list_to_bytes(output)


def gen_fault_cipher(in_put, sk, inject_round, verbose=1):
    """
        Generate faulty cipher
        :param in_put: the input plaintext, as byte
        :param sk: key schedule, as int list
        :param inject_round: the round for  injecting fault
        :param verbose: verbosity level
        :return the faulty cipher, as byte 
    """
    in_put = bytes_to_list(in_put)
    out_put = []
    ulbuf = [0]*36
    ulbuf[0:4] = byte2slices(in_put)
    for idx in range(32):
        if idx is inject_round:
            #Simulate random fault and random offset of the fault 
            diff = random.randint(1,2**8 - 1)
            offset = random.randrange(0,25, 8)
            index = random.randint(1,3)
            if(verbose > 3):
                print("round %d:Inject diff 0x%.2x at offset %d"% (inject_round, diff, offset))
            ulbuf[idx + index] ^= diff << offset
        ulbuf[idx + 4] = f_function(ulbuf[idx], ulbuf[idx + 1], ulbuf[idx + 2], ulbuf[idx + 3], sk[idx])
    out_put += put_uint32_be(ulbuf[35])
    out_put += put_uint32_be(ulbuf[34])
    out_put += put_uint32_be(ulbuf[33])
    out_put += put_uint32_be(ulbuf[32])

    return list_to_bytes(out_put)

def decrypt_round(in_put, last_round_key, verbose=1):
    output = []
    ulbuf = [0]*36
    ulbuf[0:4] = byte2slices(in_put)
    round_num = len(last_round_key)
    for idx in range(round_num):
        ulbuf[idx + 4] = f_function(ulbuf[idx], ulbuf[idx + 1], ulbuf[idx + 2], ulbuf[idx + 3], last_round_key[idx])
        if verbose > 3:
            print("decrypt round in %d:%x" % ( idx, ulbuf[idx + 4])) 
    output += put_uint32_be(ulbuf[round_num])
    output += put_uint32_be(ulbuf[round_num + 1])
    output += put_uint32_be(ulbuf[round_num + 2])
    output += put_uint32_be(ulbuf[round_num + 3] )
    return list_to_bytes(output)


def crack_round(roundFaultList, ref, last_round_key = [], verbose=1):
    """
        Crack the round key from the faulty cipher and correct cipher

        :param roundFaultList: the list with faulty ciphers, as byte list
        :param ref the correct: cipher, as byte
        :param last_round_key:  for decrypting the faulty cipher and correct cipher if not empty, as int list
        :param verbose: verbosity level
        :return: the next round key or None if the key not intact
    """
    if not last_round_key:
        pass
    else:
        """
            if last round key is not empty: require to decrypt the cipher by it
        """
        ref  = decrypt_round(ref, last_round_key, verbose)
        for index in range(len(roundFaultList)):
            roundFaultList[index] = decrypt_round(roundFaultList[index], last_round_key, verbose)
    return crack_bytes(roundFaultList, ref, verbose)
        
def check(output, encrypt=None, verbose=1, init=False, _intern={}):
    """
    Checks an output against a reference.
    The first call to the function sets the internal reference as the given output
    :param output: potentially faulty output
    :param encrypt: True if encryption, False if decryption
    :param verbose: verbosity level, prints only if verbose>2
    :param init: if True, resets the internal reference as the given output
    :returns: a FaultStatus and the index for cracking key
    """
    if init:
        _intern.clear()

    if not _intern:
        _intern['goldenref']=output
        if verbose>2:
            print("FI: record golden ref")
        return (FaultStatus.NoFault, None)
    if output == _intern['goldenref']:
        if verbose>2:
            print("FI: no impact")
        return (FaultStatus.NoFault, None)
    #diff = int2bytes(output ^ _intern['goldenref'], blockSize)
    diff = xor(output, _intern['goldenref'])
    #record the index of difference
    diffmap=[i for i in range(len(diff)) if diff[i] != 0]
    diffsum=len(diffmap)
    status = FaultStatus.Loop
    """
    SM4 always put the updated data at left hand side,
    so the fist four diff will never be equal to 0
    """
    if diffsum == 5 or diffsum == 8 or diffsum == 9 or diffsum == 12 or diffsum == 13  :
        """
            The target cipher in round 31 for analysising the round key always contains five bytes difference
            And the index of the four/eight/twelve difference indicates the position of the S-BOX for cracking the key byte.
        """
        if  check_diff(diffmap, diffsum):
            if verbose>2:
                if diffsum == 5:
                    print("FI: good candidate for round31!")
                if diffsum == 9 or diffsum == 8:
                    print("FI: good candidate for round30!")
                if diffsum == 13 or diffsum ==12:
                    print("FI: good candidate for round29!")
                if diffsum == 5:
                    status = FaultStatus.round31Fault
                if diffsum == 9 or diffsum == 8:
                    status = FaultStatus.round30Fault
                if  diffsum ==12 or diffsum == 13:
                    status = FaultStatus.round29Fault
            #big endian int, transform the index 
            return (status, (3 - diffmap[diffsum - 1] %4))
        else:
            if verbose>2:
                print("FI: wrong candidate  (%2i)" % diffsum)
            return (FaultStatus.WrongFault, None)
    elif diffsum<5:
        if verbose>2:
            print("FI: too few impact  (%2i)" % diffsum)
        return (FaultStatus.MinorFault, None)
    else:
        if verbose>2:
            print("FI: too much impact (%2i)" % diffsum)
        return (FaultStatus.MajorFault, None)

def get_candidates(faultCipher, ref,index, verbose =1):
    """
        Get the key candidates
        return the set of possible key bytes at this index
    """
    #static variable: differential distribution table in SM4
    if not hasattr(get_candidates, '_IN_TABLE'):
        get_candidates._IN_TABLE = gen_IN_table()

    faultCipher = bytes2int(faultCipher)
    ref = bytes2int(ref)
    ref_slice = getSlices(ref)
    fault_slice = getSlices(faultCipher)
    delta_C =  xor(ref_slice, fault_slice)[3]
    delta_B = l_inv(delta_C)
    A = ref_slice[0] ^ ref_slice[1] ^ ref_slice[2]
    A_star = fault_slice[0] ^ fault_slice[1] ^ fault_slice[2]
    alpha = singleState(A ^ A_star, index)
    beta = singleState(delta_B, index)
    result =  get_candidates._IN_TABLE[alpha][beta]
    if result:
        result = [singleState(A, index) ^ x for x in result]
    else:
        result = []
        print("Error: empty key candidate!")
    return result 


def crack_bytes(roundFaultList, ref,  verbose=1):
    candidates = [[], [], [] ,[]]
    key = [None] * 4
    _, index = check(ref, init=True)
    for faultCipher in roundFaultList:
        _, index = check(faultCipher)
        if index is not None:
            if key[index] is not None:
                continue
        else:
            if verbose > 2:
                print("bad fault cipher:")
                dump_byte(faultCipher)
                continue
        if verbose > 1:
            print("key index at %d" % (index))
        c = get_candidates(faultCipher, ref, index,  verbose)

        if not candidates[index]:
            #initial candidate state 
            candidates[index] = c
        else:
            candidates[index] = intersect(candidates[index], c)
            # get the exact key
            if (len(candidates[index])is 1):
                key[index] = candidates[index][0]
                if verbose>1:
                    print("Round key bytes recovered:")
                    print(''.join(["%02X" % x if x is not None else ".." for x in key]))

    #check whether all key bytes have been recovered
    for byte in key:
        if(byte is None):
            print("Only partly recovered:") 
            print(''.join(["%02X" % x if x is not None else ".." for x in key]))
            return None
    return get_uint32_le(key) 
        

def foo():
    masterKey = b'\x01\x23\x45\x67\x89\xab\xcd\xef\xfe\xdc\xba\x98\x76\x54\x32\x10'
    in_put = b'\x01\x23\x45\x67\x89\xab\xcd\xef\xfe\xdc\xba\x98\x76\x54\x32\x10'
    # last_round_key = [k31, k30, k29, k28]
    #last_round_key = [0x9124a012, 0x01cf72e5 ,0x62293496, 0x428d3654]

    sk = set_key(masterKey, SM4_ENCRYPT)
    #print("fault output:")
    r31 = [gen_fault_cipher(in_put, sk, 31) for i in range(30)]
    r30 = [gen_fault_cipher(in_put, sk, 30) for i in range(30)]
    r29 = [gen_fault_cipher(in_put, sk, 29) for i in range(30)]
    r28 = [gen_fault_cipher(in_put, sk, 28) for i in range(30)]
    ref = sm4_encrypt(in_put, sk)
    last_round_key = []
    key_schedule = []
    last_round_key.append(crack_round(r31,ref))
    last_round_key.append(crack_round(r30,ref,last_round_key))
    last_round_key.append(crack_round(r29,ref,last_round_key))
    last_round_key.append(crack_round(r28,ref,last_round_key))
    key_schedule = recovery_key(last_round_key)
    MK = get_masterKey(key_schedule)
    print("Master Key found:")
    dump_byte(MK)



    


foo()







