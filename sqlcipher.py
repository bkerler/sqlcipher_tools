# SQLCipher Tools (c) B.Kerler 2020-2021
# Licensed under MIT license
import sys
import hmac
import json
import struct, os, binascii, hashlib
from Crypto.Cipher import AES
import xml.etree.ElementTree as ET
import base64
import math
from struct import pack, unpack
from binascii import hexlify, unhexlify
from Crypto.Util import Counter

class PKCS12KDF:
    KEY_MATERIAL = 1
    IV_MATERIAL = 2
    MAC_MATERIAL = 3

    def __init__(self, password, salt, iteration_count, hash_algorithm, key_length_bits):
        self._password = password
        self._salt = salt
        self._iteration_count = iteration_count
        self._block_size_bits = None
        self._hash_length_bits = None
        self._key_length_bytes = key_length_bits // 8
        self._key = None
        self._iv = None
        self._hash_algorithm = hash_algorithm

    def copy_chunk(self, src, dstlen):
        res = b''
        for i in range(0, dstlen):
            vv = i % len(src)
            res += src[vv:vv + 1]
        return res

    def generate_derived_parameters(self, id):
        r = self._iteration_count

        if self._hash_algorithm not in hashlib.algorithms_available:
            raise ("Hash function: " + self._hash_algorithm + " not available")

        if self._hash_algorithm == "sha1":
            hash_function = hashlib.sha1
        elif self._hash_algorithm == "sha256":
            hash_function = hashlib.sha256

        v = hashlib.new(self._hash_algorithm).block_size
        u = hashlib.new(self._hash_algorithm).digest_size
        password = bytes(self._password, 'utf-16-be') + \
                   b'\x00\x00' if self._password is not None else b''
        p = len(password)
        s = len(self._salt)
        D = pack("b", id) * v
        S = b''

        if self._salt is not None:
            limit = int(float(v) * math.ceil((float(s) / float(v))))
            S = self.copy_chunk(self._salt, limit)
        else:
            S += b''

        P = b''

        if password is not None:
            limit = int(float(v) * math.ceil((float(p) / float(v))))
            P = self.copy_chunk(password, limit)
        else:
            P += b''

        I = bytearray(S) + bytearray(P)

        n = self._key_length_bytes
        result = b''

        c = int(math.ceil(float(n) / float(u)))

        for i in range(0, c):
            ctx = hash_function(D)
            ctx.update(I)
            Ai = ctx.digest()

            for j in range(1, r):
                Ai = hash_function(Ai).digest()

            result += Ai

            b_value = unpack(v * 'B', (Ai * ((v + u - 1) // u))[:v])
            new_i_value = []
            for j in range(0, len(I), v):
                # Ij = Ij + B + 1
                ij = list(unpack(v * 'B', I[j:j + v]))
                c = 1
                for k in range(v - 1, -1, -1):
                    c += ij[k] + b_value[k]
                    ij[k] = c & 0xff
                    c = c >> 8
                new_i_value.append(pack(v * 'B', *ij))
            I = b''.join(new_i_value)
        return result[:n]

    def derive(self):
        self._key = self.generate_derived_parameters(self.KEY_MATERIAL)
        self._iv = self.generate_derived_parameters(self.IV_MATERIAL)
        self._mac = self.generate_derived_parameters(self.MAC_MATERIAL)
        return self._key, self._iv, self._mac

class sqlcipher():

    def __init__(self, filename, iterations=None, version=3, pagesize=4096):
        self.filename = filename
        self.sqliteheader = b"\x53\x51\x4C\x69\x74\x65\x20\x66\x6F\x72\x6D\x61\x74\x20\x33\x00"
        self.bitlength = 256
        self.hmacsize = 0x20
        self.ivlen = 16
        self.saltlen = 16
        self.pagesize = pagesize
        self.filesize = os.stat(self.filename).st_size
        self.version = version
        if iterations is None:
            self.iterations = 4000
            if version == 3 or version == 0:
                self.iterations = 64000
        else:
            self.iterations = iterations

    def generate_hmac(self, hmac_key, content, page_no):
        hmac_obj = hmac.new(hmac_key, content, hashlib.sha1)
        hmac_obj.update(struct.pack('<i', page_no))
        return hmac_obj.digest()

    def headerdecrypt(self, fr):
        fr.seek(0)
        salt = fr.read(self.saltlen)
        if self.iterations != 0:
            key = hashlib.pbkdf2_hmac(
                'sha1', self.password, salt, self.iterations, self.bitlength // 8)
        buffer = fr.read(self.pagesize - self.ivlen - self.hmacsize)
        iv = fr.read(self.ivlen)
        hmac = fr.read(self.hmacsize)
        ctx = AES.new(key[0:self.bitlength // 8], AES.MODE_CBC, iv)
        outbuffer = ctx.decrypt(buffer)
        pagesize = struct.unpack(">H", outbuffer[0:2])[0]
        if pagesize == 0x200 or pagesize == 0x400 or pagesize == 0x1000 or pagesize == 0x2000:
            self.key = key
            self.pagesize = pagesize
            hmac_salt = bytearray()
            for x in salt:
                hmac_salt.append(x ^ 0x3a)
            hmac_key = hashlib.pbkdf2_hmac('sha1', key, hmac_salt, 2, 32)
            self.hmac_key = hmac_key
            return outbuffer
        return b""

    def verify(self):
        self.pagesize = self.pagesize - len(self.sqliteheader)

        with open(self.filename, 'rb') as fr:
            if self.version == 0:
                outbuffer = self.headerdecrypt(fr)
                if outbuffer != b"":
                    return outbuffer
                else:
                    self.hmacsize = 0
                    outbuffer = self.headerdecrypt(fr)
                    if outbuffer != b"":
                        return outbuffer
                    else:
                        self.hmacsize = 32
                        outbuffer = self.headerdecrypt(fr)
                        if outbuffer != b"":
                            return outbuffer
            else:
                self.hmacsize = 32
                outbuffer = self.headerdecrypt(fr)
                if outbuffer != b"":
                    return outbuffer
                else:
                    self.hmacsize = 0
                    outbuffer = self.headerdecrypt(fr)
                    if outbuffer != b"":
                        return outbuffer
        return b""

    def walChecksumBytes(self, data, nByte, aIn):
        s1 = aIn[0]
        s2 = aIn[1]
        for pos in range(0, nByte, 2 * 4):
            s1 += (struct.unpack("<I", data[pos:pos + 4])[0] + s2) & 0xFFFFFFFF
            s2 += (struct.unpack("<I",
                                 data[pos + 4:pos + 8])[0] + s1) & 0xFFFFFFFF
        return s1 & 0xFFFFFFFF, s2 & 0xFFFFFFFF

    def verify_wal(self, filename, fix=False):
        with open(filename, "rb+") as rf:
            filesize = os.stat(filename).st_size
            if filesize == 0:
                return
            rf.seek(0x8)
            data = rf.read(4)
            pagesize = struct.unpack(">I", data[:4])[0]
            rf.seek(0x18)
            data = rf.read(8)
            chksum1 = struct.unpack(">I", data[:4])[0]
            chksum2 = struct.unpack(">I", data[4:8])[0]

            for pos in range(0x20, filesize, pagesize + 0x18):
                rf.seek(pos)
                aFrame = rf.read(8)
                chksum1, chksum2 = self.walChecksumBytes(
                    aFrame, 8, [chksum1, chksum2])
                rf.seek(pos + 0x10)
                rc1 = struct.unpack(">I", rf.read(4))[0]
                rc2 = struct.unpack(">I", rf.read(4))[0]
                aData = rf.read(pagesize)
                chksum1, chksum2 = self.walChecksumBytes(
                    aData, pagesize, [chksum1, chksum2])
                if chksum1 != rc1 or chksum2 != rc2:
                    if not fix:
                        print("Wal verification failed at pos %08X" % pos)
                        exit(0)
                    else:
                        rf.seek(pos + 0x10)
                        dta1 = struct.pack(">I", chksum1)
                        dta2 = struct.pack(">I", chksum2)
                        rf.write(dta1)
                        rf.write(dta2)
            print("Repaired wal successfully")

    def decrypt(self, outfilename, password):
        self.password = password
        outbuffer = self.verify()
        if outbuffer == b"":
            return False
        with open(self.filename, 'rb') as fr:
            fr.seek(0)
            with open(outfilename, "wb") as wf:
                wf.write(self.sqliteheader)
                wf.write(outbuffer)
                wf.write(b'\x00' * (self.ivlen + self.hmacsize))
                i = 1
                for pos in range(self.pagesize, self.filesize, self.pagesize):
                    fr.seek(pos)
                    page_content = fr.read(
                        self.pagesize - self.ivlen - self.hmacsize)
                    iv = fr.read(self.ivlen)
                    hmac = fr.read(self.hmacsize)[:20]
                    hmac_new = self.generate_hmac(
                        self.hmac_key, page_content + iv, i + 1)
                    if not hmac == hmac_new:
                        raise RuntimeError(
                            'hmac check failed in page %d.' % (i + 1))
                    ctx = AES.new(
                        self.key[0:self.bitlength // 8], AES.MODE_CBC, iv)
                    decrypted = ctx.decrypt(page_content)
                    wf.write(decrypted)
                    wf.write(b'\x00' * (self.ivlen + self.hmacsize))
                    i += 1

        if os.path.exists(self.filename + "-wal"):
            filesize = os.stat(self.filename + "-wal").st_size
            if filesize == 0:
                return True
            with open(self.filename + "-wal", 'rb') as fr:
                with open(outfilename + "-wal", 'wb') as wf:
                    walhdr = fr.read(32)
                    if walhdr != b'':
                        wf.write(walhdr)
                        pagesize = struct.unpack(">I", walhdr[8:8 + 4])[0]
                        pos = 32
                        try:
                            while (pos < filesize):
                                frameheader = fr.read(24)
                                pgno = struct.unpack(">I", frameheader[:4])[0]
                                if pgno == 1:
                                    kdf = fr.read(16)
                                    data = fr.read(
                                        pagesize - self.ivlen - self.hmacsize - 16)
                                else:
                                    data = fr.read(
                                        pagesize - self.ivlen - self.hmacsize)
                                iv = fr.read(self.ivlen)
                                hmac = fr.read(self.hmacsize)
                                ctx = AES.new(
                                    self.key[0:self.bitlength // 8], AES.MODE_CBC, iv=iv)
                                decrypted = ctx.decrypt(data)
                                if pgno == 1:
                                    decrypted = self.sqliteheader + decrypted
                                pos += 24 + pagesize
                                wf.write(frameheader)
                                wf.write(decrypted)
                                wf.write(b'\x00' * (self.ivlen + self.hmacsize))

                        except:
                            pos = pos
            self.verify_wal(outfilename + "-wal", True)
            return True


def PKCS5PaddingLength(data):
    length = data[len(data)-1]
    if ((length > 0) and (length < 16)):
        for i in range(0, length):
            if length != data[len(data)-i-1]:
                return 0
    else:
        return 0
    return length


def getKeyFromPassphrase(passphrase, salt, iterations, encryptedAndMacdData):
    # PBEWITHSHA1AND128BITAES-CBC-BC
    key, iv, mac = PKCS12KDF(
        passphrase, salt, iterations, "sha1", 128).derive()
    return key


def getMacForPassphrase(passphrase, macSalt, iterations, encryptedAndMacdData):
    pbkdf2 = getKeyFromPassphrase(
        passphrase, macSalt, iterations, encryptedAndMacdData)
    return pbkdf2


def verifyMac(macSalt, iterations, encryptedAndMacdData, passphrase):
    pbkdf2 = getMacForPassphrase(
        passphrase, macSalt, iterations, encryptedAndMacdData)
    encryptedData = encryptedAndMacdData[:-20]
    givenMac = encryptedAndMacdData[-20:]
    localMac = hmac.new(pbkdf2, encryptedData, hashlib.sha1).digest()
    if givenMac == localMac:
        return encryptedData


def decryptWithPassphrase(encryptionSalt, iterations, data, passwd):
    # PBEWITHSHA1AND128BITAES-CBC-BC
    key, iv, mac = PKCS12KDF(passwd, encryptionSalt,
                             iterations, "sha1", 128).derive()
    aes = AES.new(key, AES.MODE_CBC, iv)
    data = aes.decrypt(data)
    padlen = PKCS5PaddingLength(data)
    data = data[:-padlen]
    return data, iv


def autodecrypt(key, dbfile, outfile):
    password = []
    try:
        password.append(bytes.fromhex(key))
        password.append(b"x'" + bytes(key,'utf-8') + b"'")
    except:
        pass
    try:
        password.append(bytes(key,'utf-8'))
        password.append(b"x'" + binascii.hexlify(key) + b"'")
    except:
        pass
    try:
        tmp=""
        for k in key:
            tmp+="%02x" % ord(k)
        password.append(bytes(tmp,'utf-8'))
        password.append(b"x'" + bytes(tmp,'utf-8') + b"'")
    except:
        pass
    kversion=""
    sqlc = None
    for key in password:
        dbfile = dbfile.replace("\\", "/")
        for version in [3,4]:
            sqlc = sqlcipher(filename=dbfile, version=version)
            if not sqlc.decrypt(outfile, key):
                sqlc = sqlcipher(filename=dbfile, iterations=1, version=3) #Signal specific
                if not sqlc.decrypt(outfile, key):
                    kversion = str(version)
                    break
            else:
                kversion = str(version)
                break
        if kversion!="":
            break

    if kversion=="":
        print("Error on decrypting database " + dbfile)
    else:
        print(f"SQLCipher Version detected: {kversion}, Iterations: {sqlc.iterations}, Key={hexlify(key).decode('utf-8')}.")
        print(f"File successfully decrypted to: {outfile}.")


if __name__ == "__main__":
    print("SQLCipher Decryptor (c) B.Kerler 2018-2021")
    if len(sys.argv)<3:
        print("Usage: python sqlcipher.py [database.sqlite] [key as hexstring]")
        print("Example: python sqlcipher.py secret.db e645b5f020b1cc2393b1c44462724321cacba071e330eb737679fdbccb9626e0")
        sys.exit(1)
    autodecrypt(sys.argv[2],sys.argv[1],sys.argv[1]+".dec.sqlite")
