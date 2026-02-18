#!/usr/bin/env python3
"""
╔══════════════════════════════════════════════════════════════════════════╗
║            CHESS SERVER — Terminal Chess Multiplayer Server              ║
║                                                                          ║
║  Features:                                                               ║
║   • User authentication (register/login with username, password, email)  ║
║   • User profile management                                              ║
║   • Game history storage (past 3 games per user)                         ║
║   • Profile viewing for other users                                      ║
║   • TCP-based client/server communication                                ║
║   • JSON-based persistent database                                       ║
╚══════════════════════════════════════════════════════════════════════════╝
"""

import socket
import threading
import json
import hashlib
import struct
import os
import re
import time
import secrets
import base64
from datetime import datetime
from hmac import compare_digest

# ════════════════════════════════════════════════════════════════════════
#  E2E ENCRYPTION UTILITIES (Pure Python stdlib - AES-GCM + ECDH-like)
# ════════════════════════════════════════════════════════════════════════

def _xor_bytes(a: bytes, b: bytes) -> bytes:
    """XOR two byte strings."""
    return bytes(x ^ y for x, y in zip(a, b))

def _pad_pkcs7(data: bytes, block_size: int = 16) -> bytes:
    """Pad data using PKCS7."""
    pad_len = block_size - (len(data) % block_size)
    return data + bytes([pad_len] * pad_len)

def _unpad_pkcs7(data: bytes) -> bytes:
    """Remove PKCS7 padding."""
    pad_len = data[-1]
    if pad_len < 1 or pad_len > 16:
        raise ValueError("Invalid padding")
    if not compare_digest(data[-pad_len:], bytes([pad_len] * pad_len)):
        raise ValueError("Invalid padding")
    return data[:-pad_len]

def _bytes_to_int(b: bytes) -> int:
    """Convert bytes to integer (big-endian)."""
    return int.from_bytes(b, 'big')

def _int_to_bytes(n: int, length: int = 256) -> bytes:
    """Convert integer to bytes (big-endian). Default 256 bytes for 2048-bit DH."""
    return n.to_bytes(length, 'big')

def _mod_pow(base: int, exp: int, mod: int) -> int:
    """Modular exponentiation."""
    result = 1
    base = base % mod
    while exp > 0:
        if exp & 1:
            result = (result * base) % mod
        exp >>= 1
        base = (base * base) % mod
    return result

# 2048-bit MODP Group (RFC 3526)
_DH_P = int(
    "FFFFFFFFFFFFFFFFC90FDAA22168C234C4C6628B80DC1CD1"
    "29024E088A67CC74020BBEA63B139B22514A08798E3404DD"
    "EF9519B3CD3A431B302B0A6DF25F14374FE1356D6D51C245"
    "E485B576625E7EC6F44C42E9A637ED6B0BFF5CB6F406B7ED"
    "EE386BFB5A899FA5AE9F24117C4B1FE649286651ECE45B3D"
    "C2007CB8A163BF0598DA48361C55D39A69163FA8FD24CF5F"
    "83655D23DCA3AD961C62F356208552BB9ED529077096966D"
    "670C354E4ABC9804F1746C08CA18217C32905E462E36CE3B"
    "E39E772C180E86039B2783A2EC07A28FB5C55DF06F4C52C9"
    "DE2BCBF6955817183995497CEA956AE515D2261898FA0510"
    "15728E5A8AACAA68FFFFFFFFFFFFFFFF", 16
)
_DH_G = 2
_DH_PRIVATE_BITS = 256

def _dh_generate_keypair():
    """Generate Diffie-Hellman key pair."""
    private_key = secrets.randbits(_DH_PRIVATE_BITS)
    public_key = _mod_pow(_DH_G, private_key, _DH_P)
    return private_key, public_key

def _dh_compute_shared_secret(private_key: int, other_public: int) -> bytes:
    """Compute DH shared secret and derive AES key."""
    shared = _mod_pow(other_public, private_key, _DH_P)
    # Derive 256-bit key using HKDF-like construction
    return hashlib.sha256(_int_to_bytes(shared)).digest()

def _aes_encrypt_block(block: bytes, key: bytes) -> bytes:
    """AES-256 encryption (pure Python implementation)."""
    # AES S-box
    SBOX = bytes([
        0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76,
        0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0,
        0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15,
        0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75,
        0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84,
        0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf,
        0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8,
        0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2,
        0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73,
        0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb,
        0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79,
        0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08,
        0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a,
        0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e,
        0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf,
        0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16,
    ])
    
    # Round constants
    RCON = [0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36, 0x6c, 0xd8, 0xab, 0x4d, 0x9a]
    
    def sub_bytes(state):
        return [SBOX[b] for b in state]
    
    def shift_rows(state):
        s = state[:]
        # Row 1: shift left by 1
        s[1], s[5], s[9], s[13] = state[5], state[9], state[13], state[1]
        # Row 2: shift left by 2
        s[2], s[6], s[10], s[14] = state[10], state[14], state[2], state[6]
        # Row 3: shift left by 3
        s[3], s[7], s[11], s[15] = state[15], state[3], state[7], state[11]
        return s
    
    def xtime(a):
        return ((a << 1) ^ 0x1b) & 0xff if a & 0x80 else (a << 1) & 0xff
    
    def mix_single_column(col):
        t = col[0] ^ col[1] ^ col[2] ^ col[3]
        u = col[0]
        col[0] ^= t ^ xtime(col[0] ^ col[1])
        col[1] ^= t ^ xtime(col[1] ^ col[2])
        col[2] ^= t ^ xtime(col[2] ^ col[3])
        col[3] ^= t ^ xtime(col[3] ^ u)
        return col
    
    def mix_columns(state):
        s = state[:]
        for i in range(4):
            col = mix_single_column(s[i*4:(i+1)*4])
            s[i*4:(i+1)*4] = col
        return s
    
    def add_round_key(state, round_key):
        return [s ^ k for s, k in zip(state, round_key)]
    
    def key_expansion(key):
        key_schedule = list(key)
        for i in range(4, 60):
            temp = key_schedule[(i-1)*4:(i)*4]
            if i % 4 == 0:
                temp = [SBOX[temp[1]], SBOX[temp[2]], SBOX[temp[3]], SBOX[temp[0]]]
                temp[0] ^= RCON[i//4 - 1]
            for j in range(4):
                key_schedule.append(key_schedule[(i-4)*4 + j] ^ temp[j])
        return key_schedule
    
    # Key expansion
    key_schedule = key_expansion(key)
    
    # Initial state
    state = list(block)
    
    # Initial round key addition
    state = add_round_key(state, key_schedule[:16])
    
    # Main rounds (14 rounds for AES-256)
    for round_num in range(1, 14):
        state = sub_bytes(state)
        state = shift_rows(state)
        state = mix_columns(state)
        state = add_round_key(state, key_schedule[round_num*16:(round_num+1)*16])
    
    # Final round (no MixColumns)
    state = sub_bytes(state)
    state = shift_rows(state)
    state = add_round_key(state, key_schedule[14*16:15*16])
    
    return bytes(state)

def _aes_decrypt_block(block: bytes, key: bytes) -> bytes:
    """AES-256 decryption (pure Python implementation)."""
    # AES inverse S-box
    INV_SBOX = bytes([
        0x52, 0x09, 0x6a, 0xd5, 0x30, 0x36, 0xa5, 0x38, 0xbf, 0x40, 0xa3, 0x9e, 0x81, 0xf3, 0xd7, 0xfb,
        0x7c, 0xe3, 0x39, 0x82, 0x9b, 0x2f, 0xff, 0x87, 0x34, 0x8e, 0x43, 0x44, 0xc4, 0xde, 0xe9, 0xcb,
        0x54, 0x7b, 0x94, 0x32, 0xa6, 0xc2, 0x23, 0x3d, 0xee, 0x4c, 0x95, 0x0b, 0x42, 0xfa, 0xc3, 0x4e,
        0x08, 0x2e, 0xa1, 0x66, 0x28, 0xd9, 0x24, 0xb2, 0x76, 0x5b, 0xa2, 0x49, 0x6d, 0x8b, 0xd1, 0x25,
        0x72, 0xf8, 0xf6, 0x64, 0x86, 0x68, 0x98, 0x16, 0xd4, 0xa4, 0x5c, 0xcc, 0x5d, 0x65, 0xb6, 0x92,
        0x6c, 0x70, 0x48, 0x50, 0xfd, 0xed, 0xb9, 0xda, 0x5e, 0x15, 0x46, 0x57, 0xa7, 0x8d, 0x9d, 0x84,
        0x90, 0xd8, 0xab, 0x00, 0x8c, 0xbc, 0xd3, 0x0a, 0xf7, 0xe4, 0x58, 0x05, 0xb8, 0xb3, 0x45, 0x06,
        0xd0, 0x2c, 0x1e, 0x8f, 0xca, 0x3f, 0x0f, 0x02, 0xc1, 0xaf, 0xbd, 0x03, 0x01, 0x13, 0x8a, 0x6b,
        0x3a, 0x91, 0x11, 0x41, 0x4f, 0x67, 0xdc, 0xea, 0x97, 0xf2, 0xcf, 0xce, 0xf0, 0xb4, 0xe6, 0x73,
        0x96, 0xac, 0x74, 0x22, 0xe7, 0xad, 0x35, 0x85, 0xe2, 0xf9, 0x37, 0xe8, 0x1c, 0x75, 0xdf, 0x6e,
        0x47, 0xf1, 0x1a, 0x71, 0x1d, 0x29, 0xc5, 0x89, 0x6f, 0xb7, 0x62, 0x0e, 0xaa, 0x18, 0xbe, 0x1b,
        0xfc, 0x56, 0x3e, 0x4b, 0xc6, 0xd2, 0x79, 0x20, 0x9a, 0xdb, 0xc0, 0xfe, 0x78, 0xcd, 0x5a, 0xf4,
        0x1f, 0xdd, 0xa8, 0x33, 0x88, 0x07, 0xc7, 0x31, 0xb1, 0x12, 0x10, 0x59, 0x27, 0x80, 0xec, 0x5f,
        0x60, 0x51, 0x7f, 0xa9, 0x19, 0xb5, 0x4a, 0x0d, 0x2d, 0xe5, 0x7a, 0x9f, 0x93, 0xc9, 0x9c, 0xef,
        0xa0, 0xe0, 0x3b, 0x4d, 0xae, 0x2a, 0xf5, 0xb0, 0xc8, 0xeb, 0xbb, 0x3c, 0x83, 0x53, 0x99, 0x61,
        0x17, 0x2b, 0x04, 0x7e, 0xba, 0x77, 0xd6, 0x26, 0xe1, 0x69, 0x14, 0x63, 0x55, 0x21, 0x0c, 0x7d,
    ])
    
    RCON = [0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36, 0x6c, 0xd8, 0xab, 0x4d, 0x9a]
    
    def inv_sub_bytes(state):
        return [INV_SBOX[b] for b in state]
    
    def inv_shift_rows(state):
        s = state[:]
        s[1], s[5], s[9], s[13] = state[13], state[1], state[5], state[9]
        s[2], s[6], s[10], s[14] = state[10], state[14], state[2], state[6]
        s[3], s[7], s[11], s[15] = state[7], state[11], state[15], state[3]
        return s
    
    def inv_mix_columns(state):
        s = state[:]
        for i in range(4):
            a = s[i*4:(i+1)*4]
            s[i*4] = (0x0e * a[0]) ^ (0x0b * a[1]) ^ (0x0d * a[2]) ^ (0x09 * a[3])
            s[i*4+1] = (0x09 * a[0]) ^ (0x0e * a[1]) ^ (0x0b * a[2]) ^ (0x0d * a[3])
            s[i*4+2] = (0x0d * a[0]) ^ (0x09 * a[1]) ^ (0x0e * a[2]) ^ (0x0b * a[3])
            s[i*4+3] = (0x0b * a[0]) ^ (0x0d * a[1]) ^ (0x09 * a[2]) ^ (0x0e * a[3])
        return s
    
    def gmul(a, b):
        p = 0
        for _ in range(8):
            if b & 1:
                p ^= a
            hi_bit = a & 0x80
            a = (a << 1) & 0xff
            if hi_bit:
                a ^= 0x1b
            b >>= 1
        return p
    
    def key_expansion(key):
        key_schedule = list(key)
        for i in range(4, 60):
            temp = key_schedule[(i-1)*4:(i)*4]
            if i % 4 == 0:
                temp = [INV_SBOX[temp[1]], INV_SBOX[temp[2]], INV_SBOX[temp[3]], INV_SBOX[temp[0]]]
                temp[0] ^= RCON[i//4 - 1]
            for j in range(4):
                key_schedule.append(key_schedule[(i-4)*4 + j] ^ temp[j])
        return key_schedule
    
    key_schedule = key_expansion(key)
    state = list(block)
    state = add_round_key(state, key_schedule[14*16:15*16])
    
    for round_num in range(13, 0, -1):
        state = inv_shift_rows(state)
        state = inv_sub_bytes(state)
        state = add_round_key(state, key_schedule[round_num*16:(round_num+1)*16])
        if round_num > 1:
            state = inv_mix_columns(state)
    
    state = inv_shift_rows(state)
    state = inv_sub_bytes(state)
    state = add_round_key(state, key_schedule[:16])
    
    return bytes(state)

def _aes_ctr_encrypt(plaintext: bytes, key: bytes, nonce: bytes) -> bytes:
    """AES-256 CTR mode encryption."""
    result = bytearray()
    counter = 0
    for i in range(0, len(plaintext), 16):
        counter_block = nonce + _int_to_bytes(counter, 4)[:4]
        keystream = _aes_encrypt_block(counter_block, key)
        block = plaintext[i:i+16]
        encrypted = _xor_bytes(block, keystream[:len(block)])
        result.extend(encrypted)
        counter += 1
    return bytes(result)

def _aes_ctr_decrypt(ciphertext: bytes, key: bytes, nonce: bytes) -> bytes:
    """AES-256 CTR mode decryption (same as encryption for CTR mode)."""
    return _aes_ctr_encrypt(ciphertext, key, nonce)

def _ghash(h: bytes, data: bytes) -> bytes:
    """GHASH for GCM mode."""
    def gf_mult(x: int, y: int) -> int:
        z = 0
        for i in range(128):
            if (x >> (127 - i)) & 1:
                z ^= y
            if y & 1:
                y = (y >> 1) ^ 0xe1000000000000000000000000000000
            else:
                y >>= 1
        return z
    
    h_int = _bytes_to_int(h)
    result = 0
    for i in range(0, len(data), 16):
        block = data[i:i+16]
        if len(block) < 16:
            block = block + b'\x00' * (16 - len(block))
        result = gf_mult(result ^ _bytes_to_int(block), h_int)
    return _int_to_bytes(result, 16)

def _gcm_encrypt(plaintext: bytes, key: bytes, nonce: bytes, aad: bytes = b'') -> tuple:
    """AES-GCM encryption."""
    # Generate H (hash key)
    h = _aes_encrypt_block(b'\x00' * 16, key)
    
    # Initial counter
    j0 = nonce + b'\x00\x00\x00\x01' if len(nonce) == 12 else nonce + b'\x00' * (16 - len(nonce) % 16) + b'\x00\x00\x00\x01'
    
    # Encrypt plaintext
    ciphertext = _aes_ctr_encrypt(plaintext, key, j0[:12])
    
    # Compute GHASH
    ghash_input = aad + b'\x00' * ((16 - len(aad) % 16) % 16) if aad else b''
    ghash_input += ciphertext + b'\x00' * ((16 - len(ciphertext) % 16) % 16)
    ghash_input += _int_to_bytes(len(aad) * 8, 8) + _int_to_bytes(len(ciphertext) * 8, 8)
    
    s = _ghash(h, ghash_input)
    
    # Compute tag
    tag_input = _aes_encrypt_block(j0, key)
    tag = _xor_bytes(s, tag_input)
    
    return ciphertext, tag

def _gcm_decrypt(ciphertext: bytes, key: bytes, nonce: bytes, tag: bytes, aad: bytes = b'') -> bytes:
    """AES-GCM decryption."""
    h = _aes_encrypt_block(b'\x00' * 16, key)
    
    j0 = nonce + b'\x00\x00\x00\x01' if len(nonce) == 12 else nonce + b'\x00' * (16 - len(nonce) % 16) + b'\x00\x00\x00\x01'
    
    # Verify tag first
    ghash_input = aad + b'\x00' * ((16 - len(aad) % 16) % 16) if aad else b''
    ghash_input += ciphertext + b'\x00' * ((16 - len(ciphertext) % 16) % 16)
    ghash_input += _int_to_bytes(len(aad) * 8, 8) + _int_to_bytes(len(ciphertext) * 8, 8)
    
    s = _ghash(h, ghash_input)
    tag_input = _aes_encrypt_block(j0, key)
    computed_tag = _xor_bytes(s, tag_input)
    
    if not compare_digest(computed_tag, tag):
        raise ValueError("Authentication tag verification failed")
    
    plaintext = _aes_ctr_decrypt(ciphertext, key, j0[:12])
    return plaintext

def encrypt_credentials(credentials: dict, server_public: int) -> dict:
    """Encrypt credentials using ECDH + AES-GCM."""
    # Generate ephemeral key pair
    client_private, client_public = _dh_generate_keypair()
    
    # Compute shared secret
    shared_secret = _dh_compute_shared_secret(client_private, server_public)
    
    # Serialize credentials
    credentials_json = json.dumps(credentials).encode('utf-8')
    
    # Generate random nonce
    nonce = secrets.token_bytes(12)
    
    # Encrypt with AES-GCM
    ciphertext, tag = _gcm_encrypt(credentials_json, shared_secret, nonce)
    
    return {
        'client_public': client_public,
        'nonce': base64.b64encode(nonce).decode(),
        'ciphertext': base64.b64encode(ciphertext).decode(),
        'tag': base64.b64encode(tag).decode()
    }

def decrypt_credentials(encrypted_data: dict, server_private: int) -> dict:
    """Decrypt credentials using ECDH + AES-GCM."""
    client_public = encrypted_data['client_public']
    nonce = base64.b64decode(encrypted_data['nonce'])
    ciphertext = base64.b64decode(encrypted_data['ciphertext'])
    tag = base64.b64decode(encrypted_data['tag'])
    
    # Compute shared secret
    shared_secret = _dh_compute_shared_secret(server_private, client_public)
    
    # Decrypt
    plaintext = _gcm_decrypt(ciphertext, shared_secret, nonce, tag)
    
    return json.loads(plaintext.decode('utf-8'))

# ════════════════════════════════════════════════════════════════════════
#  CONSTANTS
# ════════════════════════════════════════════════════════════════════════
SERVER_PORT = 65433
DATABASE_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'database.json')
MAX_GAMES_PER_USER = 3

# ════════════════════════════════════════════════════════════════════════
#  MESSAGE TYPES
# ════════════════════════════════════════════════════════════════════════
MSG_REGISTER = 'REGISTER'
MSG_LOGIN = 'LOGIN'
MSG_AUTO_LOGIN = 'AUTO_LOGIN'
MSG_LOGOUT = 'LOGOUT'
MSG_GET_PROFILE = 'GET_PROFILE'
MSG_SAVE_GAME = 'SAVE_GAME'
MSG_LIST_USERS = 'LIST_USERS'
MSG_PING = 'PING'
MSG_LEADERBOARD = 'LEADERBOARD'

# Matchmaking message types
MSG_QUEUE_JOIN = 'QUEUE_JOIN'
MSG_QUEUE_LEAVE = 'QUEUE_LEAVE'
MSG_QUEUE_STATUS = 'QUEUE_STATUS'
MSG_MATCH_FOUND = 'MATCH_FOUND'
MSG_MATCH_ACCEPT = 'MATCH_ACCEPT'
MSG_MATCH_DECLINE = 'MATCH_DECLINE'
MSG_GAME_START = 'GAME_START'
MSG_GAME_MOVE = 'GAME_MOVE'
MSG_GAME_RESIGN = 'GAME_RESIGN'
MSG_GAME_DRAW_OFFER = 'GAME_DRAW_OFFER'
MSG_GAME_DRAW_ACCEPT = 'GAME_DRAW_ACCEPT'
MSG_GAME_CHAT = 'GAME_CHAT'

# Friend system message types
MSG_FRIEND_REQUEST = 'FRIEND_REQUEST'
MSG_FRIEND_RESPONSE = 'FRIEND_RESPONSE'
MSG_FRIEND_LIST = 'FRIEND_LIST'
MSG_FRIEND_REMOVE = 'FRIEND_REMOVE'
MSG_FRIEND_STATUS = 'FRIEND_STATUS'

# Messaging system message types
MSG_KEY_EXCHANGE = 'KEY_EXCHANGE'
MSG_SEND_MESSAGE = 'SEND_MESSAGE'
MSG_GET_MESSAGES = 'GET_MESSAGES'
MSG_NEW_MESSAGE_NOTIFY = 'NEW_MESSAGE_NOTIFY'
MSG_MESSAGES_DELETED = 'MESSAGES_DELETED'

# Challenge system message types
MSG_CHALLENGE_SEND = 'CHALLENGE_SEND'
MSG_CHALLENGE_RESPONSE = 'CHALLENGE_RESPONSE'
MSG_CHALLENGE_LIST = 'CHALLENGE_LIST'
MSG_CHALLENGE_CANCEL = 'CHALLENGE_CANCEL'

# E2E Encryption message types
MSG_GET_SERVER_PUBLIC_KEY = 'GET_SERVER_PUBLIC_KEY'
MSG_SESSION_KEY_EXCHANGE = 'SESSION_KEY_EXCHANGE'

# Response types
RESP_SUCCESS = 'SUCCESS'
RESP_ERROR = 'ERROR'
RESP_PROFILE = 'PROFILE'
RESP_USERS = 'USERS'
RESP_QUEUED = 'QUEUED'
RESP_MATCH = 'MATCH'
RESP_LEADERBOARD = 'LEADERBOARD'

# ════════════════════════════════════════════════════════════════════════
#  DATABASE MANAGER
# ════════════════════════════════════════════════════════════════════════
class DatabaseManager:
    """Handles all database operations for user accounts and game history."""
    
    def __init__(self, db_file=DATABASE_FILE):
        self.db_file = db_file
        self.lock = threading.Lock()
        self._init_db()
    
    def _init_db(self):
        """Initialize database file if it doesn't exist."""
        if not os.path.exists(self.db_file):
            self._save_db({
                "users": {},
                "game_history": [],
                "friend_requests": [],
                "friendships": [],
                "messages": [],
                "challenges": []
            })
    
    def _load_db(self):
        """Load database from file."""
        try:
            with open(self.db_file, 'r') as f:
                return json.load(f)
        except (json.JSONDecodeError, FileNotFoundError):
            return {"users": {}, "game_history": []}
    
    def _save_db(self, data):
        """Save database to file."""
        with open(self.db_file, 'w') as f:
            json.dump(data, f, indent=2)
    
    def _hash_password(self, password):
        """Hash password using SHA-256."""
        return hashlib.sha256(password.encode()).hexdigest()
    
    def _validate_email(self, email):
        """Validate email format."""
        pattern = r'^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}$'
        return re.match(pattern, email) is not None
    
    def _validate_username(self, username):
        """Validate username format."""
        if len(username) < 3 or len(username) > 20:
            return False
        return re.match(r'^[a-zA-Z0-9_]+$', username) is not None
    
    def register_user(self, username, password, email):
        """
        Register a new user.
        Returns (success, message) tuple.
        """
        with self.lock:
            db = self._load_db()
            
            # Validate username
            if not self._validate_username(username):
                return False, "Username must be 3-20 characters (alphanumeric and underscore only)"
            
            # Validate email
            if not self._validate_email(email):
                return False, "Invalid email format"
            
            # Validate password
            if len(password) < 6:
                return False, "Password must be at least 6 characters"
            
            # Check if username exists
            if username in db['users']:
                return False, "Username already exists"
            
            # Check if email exists
            for user_data in db['users'].values():
                if user_data['email'] == email:
                    return False, "Email already registered"
            
            # Create user
            db['users'][username] = {
                'password_hash': self._hash_password(password),
                'email': email,
                'created_at': datetime.now().isoformat(),
                'games_played': 0,
                'wins': 0,
                'losses': 0,
                'draws': 0,
                'elo': 1200,  # Starting ELO (like chess.com rapid)
                'elo_games': 0,
                'elo_wins': 0,
                'elo_losses': 0,
                'elo_draws': 0,
                'elo_peak': 1200
            }

            self._save_db(db)
            return True, "Registration successful"
    
    def authenticate_user(self, username, password):
        """
        Authenticate user login.
        Returns (success, message) tuple.
        """
        with self.lock:
            db = self._load_db()

            if username not in db['users']:
                return False, "Invalid username or password"

            password_hash = self._hash_password(password)
            if db['users'][username]['password_hash'] != password_hash:
                return False, "Invalid username or password"

            return True, "Login successful"

    def authenticate_user_with_hash(self, username, password_hash):
        """
        Authenticate user login using stored password hash (for auto-login).
        Returns (success, message) tuple.
        """
        with self.lock:
            db = self._load_db()

            if username not in db['users']:
                return False, "Invalid username or password"

            if db['users'][username]['password_hash'] != password_hash:
                return False, "Invalid username or password"

            return True, "Auto-login successful"
    
    def get_user_profile(self, username):
        """
        Get user profile information.
        Returns profile dict or None if user doesn't exist.
        """
        with self.lock:
            db = self._load_db()

            if username not in db['users']:
                return None

            user_data = db['users'][username]

            # Get user's last 3 games
            user_games = [
                g for g in db['game_history']
                if g['white'] == username or g['black'] == username
            ]
            user_games.sort(key=lambda x: x['timestamp'], reverse=True)
            recent_games = user_games[:MAX_GAMES_PER_USER]

            return {
                'username': username,
                'email': user_data['email'],
                'created_at': user_data['created_at'],
                'games_played': user_data['games_played'],
                'wins': user_data['wins'],
                'losses': user_data['losses'],
                'draws': user_data['draws'],
                'elo': user_data.get('elo', 1200),
                'elo_games': user_data.get('elo_games', 0),
                'elo_wins': user_data.get('elo_wins', 0),
                'elo_losses': user_data.get('elo_losses', 0),
                'elo_draws': user_data.get('elo_draws', 0),
                'elo_peak': user_data.get('elo_peak', 1200),
                'recent_games': recent_games
            }
    
    def _calculate_elo_change(self, rating_a, rating_b, result_a, k_factor=32):
        """
        Calculate ELO change for a player.
        result_a: 1=win, 0.5=draw, 0=loss
        Returns: (new_rating_a, new_rating_b, change_a, change_b)
        """
        # Expected score
        expected_a = 1.0 / (1.0 + 10 ** ((rating_b - rating_a) / 400.0))
        expected_b = 1.0 / (1.0 + 10 ** ((rating_a - rating_b) / 400.0))
        
        # New ratings
        change_a = k_factor * (result_a - expected_a)
        change_b = k_factor * ((1 - result_a) - expected_b)
        
        return round(rating_a + change_a), round(rating_b + change_b), round(change_a), round(change_b)

    def _get_k_factor(self, rating, games_played):
        """
        Get K-factor based on rating and experience (like chess.com).
        Higher K for new/low-rated players, lower for established/high-rated.
        """
        if games_played < 30:
            return 40  # High K for new players
        elif rating < 2000:
            return 32  # Standard K
        elif rating < 2400:
            return 24  # Lower K for experienced players
        else:
            return 16  # Lowest K for masters

    def save_game(self, white, black, result, moves, duration=0, rated=True):
        """
        Save a game to history.
        Result: 'white', 'black', or 'draw'
        If rated=True, also update ELO ratings.
        """
        with self.lock:
            db = self._load_db()

            game_record = {
                'id': len(db['game_history']) + 1,
                'timestamp': datetime.now().isoformat(),
                'white': white,
                'black': black,
                'result': result,
                'moves': moves,
                'duration': duration,
                'rated': rated
            }

            db['game_history'].append(game_record)

            elo_changes = {}  # Store ELO changes to return

            # Update user stats and ELO
            for username, color in [(white, 'white'), (black, 'black')]:
                if username in db['users']:
                    db['users'][username]['games_played'] += 1
                    if result == color:
                        db['users'][username]['wins'] += 1
                    elif result == 'draw':
                        db['users'][username]['draws'] += 1
                    else:
                        db['users'][username]['losses'] += 1

                    # Update ELO if rated
                    if rated:
                        db['users'][username]['elo_games'] += 1
                        if result == color:
                            db['users'][username]['elo_wins'] += 1
                        elif result == 'draw':
                            db['users'][username]['elo_draws'] += 1
                        else:
                            db['users'][username]['elo_losses'] += 1
                    print(f"  [DB] Updated stats for {username}: games={db['users'][username]['games_played']}, elo_games={db['users'][username].get('elo_games', 0)}")
                else:
                    print(f"  [DB] Warning: User {username} not found in database!")

            # Calculate and apply ELO changes
            if rated and white in db['users'] and black in db['users']:
                white_elo = db['users'][white]['elo']
                black_elo = db['users'][black]['elo']

                # Determine result from white's perspective
                if result == 'white':
                    white_result = 1.0
                elif result == 'black':
                    white_result = 0.0
                else:
                    white_result = 0.5

                # Get K-factors
                white_k = self._get_k_factor(white_elo, db['users'][white]['elo_games'])
                black_k = self._get_k_factor(black_elo, db['users'][black]['elo_games'])

                # Calculate expected scores
                white_expected = 1.0 / (1.0 + 10 ** ((black_elo - white_elo) / 400.0))
                black_expected = 1.0 / (1.0 + 10 ** ((white_elo - black_elo) / 400.0))

                # Calculate changes
                white_change = round(white_k * (white_result - white_expected))
                black_change = round(black_k * ((1 - white_result) - black_expected))

                # Apply changes
                new_white_elo = white_elo + white_change
                new_black_elo = black_elo + black_change

                db['users'][white]['elo'] = new_white_elo
                db['users'][black]['elo'] = new_black_elo

                # Update peak ELO
                if new_white_elo > db['users'][white]['elo_peak']:
                    db['users'][white]['elo_peak'] = new_white_elo
                if new_black_elo > db['users'][black]['elo_peak']:
                    db['users'][black]['elo_peak'] = new_black_elo

                elo_changes = {
                    'white': {'old': white_elo, 'new': new_white_elo, 'change': white_change},
                    'black': {'old': black_elo, 'new': new_black_elo, 'change': black_change}
                }
                print(f"  [DB] ELO changes calculated: {elo_changes}")

            self._save_db(db)
            print(f"  [DB] Database saved")

            if rated:
                return True, elo_changes
            return True, None
    
    def list_users(self):
        """Get list of all usernames."""
        with self.lock:
            db = self._load_db()
            return list(db['users'].keys())

    def get_leaderboard(self, limit=10):
        """Get ELO leaderboard."""
        with self.lock:
            db = self._load_db()
            users = []
            for username, data in db['users'].items():
                users.append({
                    'username': username,
                    'elo': data.get('elo', 1200),
                    'games': data.get('elo_games', 0),
                    'wins': data.get('elo_wins', 0),
                    'losses': data.get('elo_losses', 0),
                    'draws': data.get('elo_draws', 0),
                    'peak': data.get('elo_peak', 1200)
                })
            # Sort by ELO descending
            users.sort(key=lambda x: (-x['elo'], -x['games']))
            return users[:limit]

    # ════════════════════════════════════════════════════════════════════
    #  FRIEND SYSTEM METHODS
    # ════════════════════════════════════════════════════════════════════
    def send_friend_request(self, sender, recipient):
        """Send a friend request."""
        with self.lock:
            db = self._load_db()
            
            # Validate users exist
            if sender not in db['users'] or recipient not in db['users']:
                return False, "User not found"
            
            if sender == recipient:
                return False, "Cannot send friend request to yourself"
            
            # Check if already friends
            for friendship in db['friendships']:
                if (friendship['user1'] == sender and friendship['user2'] == recipient) or \
                   (friendship['user1'] == recipient and friendship['user2'] == sender):
                    return False, "Already friends"
            
            # Check for existing request
            for req in db['friend_requests']:
                if (req['sender'] == sender and req['recipient'] == recipient):
                    return False, "Friend request already sent"
            
            # Create friend request
            friend_request = {
                'id': len(db['friend_requests']) + 1,
                'sender': sender,
                'recipient': recipient,
                'created_at': datetime.now().isoformat(),
                'status': 'pending'
            }
            db['friend_requests'].append(friend_request)
            self._save_db(db)
            return True, "Friend request sent"

    def respond_to_friend_request(self, sender, recipient, accept):
        """Respond to a friend request."""
        with self.lock:
            db = self._load_db()
            
            # Find the request
            request_found = None
            for req in db['friend_requests']:
                if req['sender'] == sender and req['recipient'] == recipient:
                    request_found = req
                    break
            
            if not request_found:
                return False, "Friend request not found"
            
            if accept:
                # Create friendship
                friendship = {
                    'id': len(db['friendships']) + 1,
                    'user1': sender,
                    'user2': recipient,
                    'created_at': datetime.now().isoformat()
                }
                db['friendships'].append(friendship)
            
            # Remove the request
            db['friend_requests'] = [r for r in db['friend_requests'] if r != request_found]
            self._save_db(db)
            
            if accept:
                return True, "Friend request accepted"
            return True, "Friend request declined"

    def get_friend_requests(self, username):
        """Get pending friend requests for a user."""
        with self.lock:
            db = self._load_db()
            requests = []
            for req in db['friend_requests']:
                if req['recipient'] == username and req['status'] == 'pending':
                    requests.append({
                        'id': req['id'],
                        'sender': req['sender'],
                        'created_at': req['created_at']
                    })
            return requests

    def get_friends(self, username):
        """Get list of friends for a user."""
        with self.lock:
            db = self._load_db()
            friends = []
            for friendship in db['friendships']:
                if friendship['user1'] == username:
                    friends.append(friendship['user2'])
                elif friendship['user2'] == username:
                    friends.append(friendship['user1'])
            return friends

    def remove_friend(self, user1, user2):
        """Remove a friendship."""
        with self.lock:
            db = self._load_db()
            
            for friendship in db['friendships']:
                if (friendship['user1'] == user1 and friendship['user2'] == user2) or \
                   (friendship['user1'] == user2 and friendship['user2'] == user1):
                    db['friendships'].remove(friendship)
                    self._save_db(db)
                    return True, "Friend removed"
            
            return False, "Friendship not found"

    def are_friends(self, user1, user2):
        """Check if two users are friends."""
        with self.lock:
            db = self._load_db()
            for friendship in db['friendships']:
                if (friendship['user1'] == user1 and friendship['user2'] == user2) or \
                   (friendship['user1'] == user2 and friendship['user2'] == user1):
                    return True
            return False

    # ════════════════════════════════════════════════════════════════════
    #  MESSAGING SYSTEM METHODS
    # ════════════════════════════════════════════════════════════════════
    def store_message(self, sender, recipient, encrypted_content, iv, tag):
        """Store an encrypted message."""
        with self.lock:
            db = self._load_db()
            
            # Verify users are friends
            if not self.are_friends(sender, recipient):
                return False, "Users are not friends"
            
            message = {
                'id': len(db['messages']) + 1,
                'sender': sender,
                'recipient': recipient,
                'encrypted_content': encrypted_content,
                'iv': iv,
                'tag': tag,
                'created_at': datetime.now().isoformat(),
                'expires_at': (datetime.now().replace(hour=datetime.now().hour) + 
                              __import__('datetime').timedelta(hours=12)).isoformat()
            }
            db['messages'].append(message)
            self._save_db(db)
            return True, message['id']

    def get_messages(self, user1, user2, since_id=0):
        """Get messages between two users."""
        with self.lock:
            db = self._load_db()
            
            # Verify users are friends
            if not self.are_friends(user1, user2):
                return []
            
            messages = []
            for msg in db['messages']:
                if ((msg['sender'] == user1 and msg['recipient'] == user2) or
                    (msg['sender'] == user2 and msg['recipient'] == user1)):
                    if msg['id'] > since_id:
                        messages.append({
                            'id': msg['id'],
                            'sender': msg['sender'],
                            'encrypted_content': msg['encrypted_content'],
                            'iv': msg['iv'],
                            'tag': msg['tag'],
                            'created_at': msg['created_at']
                        })
            return messages

    def cleanup_expired_messages(self):
        """Remove messages older than 12 hours."""
        with self.lock:
            db = self._load_db()
            now = datetime.now()
            original_count = len(db['messages'])
            
            db['messages'] = [
                msg for msg in db['messages']
                if datetime.fromisoformat(msg['expires_at']) > now
            ]
            
            if len(db['messages']) < original_count:
                self._save_db(db)
                return original_count - len(db['messages'])
            return 0

    # ════════════════════════════════════════════════════════════════════
    #  CHALLENGE SYSTEM METHODS
    # ════════════════════════════════════════════════════════════════════
    def send_challenge(self, challenger, challenged, color_choice='random', rated=True):
        """Send a game challenge."""
        with self.lock:
            db = self._load_db()
            
            # Validate users exist
            if challenger not in db['users'] or challenged not in db['users']:
                return False, "User not found"
            
            if challenger == challenged:
                return False, "Cannot challenge yourself"
            
            # Verify users are friends
            if not self.are_friends(challenger, challenged):
                return False, "Can only challenge friends"
            
            # Check for existing active challenge
            for challenge in db['challenges']:
                if challenge['status'] == 'pending':
                    if ((challenge['challenger'] == challenger and challenge['challenged'] == challenged) or
                        (challenge['challenger'] == challenged and challenge['challenged'] == challenger)):
                        return False, "Pending challenge already exists"
            
            challenge = {
                'id': len(db['challenges']) + 1,
                'challenger': challenger,
                'challenged': challenged,
                'color_choice': color_choice,
                'rated': rated,
                'created_at': datetime.now().isoformat(),
                'status': 'pending'
            }
            db['challenges'].append(challenge)
            self._save_db(db)
            return True, challenge['id']

    def respond_to_challenge(self, challenger, challenged, accept):
        """Respond to a challenge."""
        with self.lock:
            db = self._load_db()
            
            # Find the challenge
            challenge_found = None
            for challenge in db['challenges']:
                if (challenge['challenger'] == challenger and 
                    challenge['challenged'] == challenged and
                    challenge['status'] == 'pending'):
                    challenge_found = challenge
                    break
            
            if not challenge_found:
                return False, "Challenge not found"
            
            if accept:
                challenge_found['status'] = 'accepted'
                # Determine colors
                import random
                if challenge_found['color_choice'] == 'random':
                    colors = ['white', 'black']
                    random.shuffle(colors)
                    challenge_found['challenger_color'] = colors[0]
                    challenge_found['challenged_color'] = colors[1]
                elif challenge_found['color_choice'] == 'white':
                    challenge_found['challenger_color'] = 'white'
                    challenge_found['challenged_color'] = 'black'
                else:
                    challenge_found['challenger_color'] = 'black'
                    challenge_found['challenged_color'] = 'white'
            else:
                challenge_found['status'] = 'declined'
            
            self._save_db(db)
            
            if accept:
                return True, {
                    'challenge_id': challenge_found['id'],
                    'challenger_color': challenge_found['challenger_color'],
                    'challenged_color': challenge_found['challenged_color'],
                    'rated': challenge_found['rated']
                }
            return True, "Challenge declined"

    def get_challenges(self, username):
        """Get pending challenges for a user."""
        with self.lock:
            db = self._load_db()
            challenges = []
            for challenge in db['challenges']:
                if challenge['status'] == 'pending':
                    if challenge['challenged'] == username or challenge['challenger'] == username:
                        challenges.append({
                            'id': challenge['id'],
                            'challenger': challenge['challenger'],
                            'challenged': challenge['challenged'],
                            'color_choice': challenge['color_choice'],
                            'rated': challenge['rated'],
                            'created_at': challenge['created_at']
                        })
            return challenges

    def cancel_challenge(self, challenger, challenged):
        """Cancel a pending challenge."""
        with self.lock:
            db = self._load_db()
            
            for challenge in db['challenges']:
                if (challenge['challenger'] == challenger and 
                    challenge['challenged'] == challenged and
                    challenge['status'] == 'pending'):
                    challenge['status'] = 'cancelled'
                    self._save_db(db)
                    return True, "Challenge cancelled"
            
            return False, "Challenge not found"


# ════════════════════════════════════════════════════════════════════════
#  MATCHMAKING MANAGER
# ════════════════════════════════════════════════════════════════════════
class MatchmakingManager:
    """Handles player queueing and match pairing."""
    
    def __init__(self):
        self.queue = {}  # username -> {rating, joined_time, handler}
        self.active_games = {}  # game_id -> {white, black, white_handler, black_handler}
        self.lock = threading.Lock()
        self.game_counter = 0
        self.matchmaking_thread = None
        self.running = True
    
    def start(self):
        """Start the matchmaking background thread."""
        self.matchmaking_thread = threading.Thread(target=self._matchmaking_loop, daemon=True)
        self.matchmaking_thread.start()
    
    def stop(self):
        """Stop the matchmaking system."""
        self.running = False
    
    def _matchmaking_loop(self):
        """Background loop to find and create matches."""
        while self.running:
            time.sleep(1.0)  # Check every second
            self._try_match_players()
    
    def _try_match_players(self):
        """Try to match players in the queue based on ELO similarity."""
        with self.lock:
            if len(self.queue) < 2:
                return

            # Get all queued players sorted by rating
            queued = sorted(self.queue.items(), key=lambda x: x[1]['rating'])

            # Find two players with similar ELO
            max_elo_diff = 200  # Maximum allowed ELO difference
            player1, player2 = None, None
            data1, data2 = None, None

            # Try to find a match with similar ELO
            for i in range(len(queued) - 1):
                p1_name, p1_data = queued[i]
                p2_name, p2_data = queued[i + 1]
                
                elo_diff = abs(p1_data['rating'] - p2_data['rating'])
                if elo_diff <= max_elo_diff:
                    player1, data1 = p1_name, p1_data
                    player2, data2 = p2_name, p2_data
                    break

            # If no similar ELO found, fall back to first two players (with warning)
            if player1 is None and len(queued) >= 2:
                player1, data1 = queued[0]
                player2, data2 = queued[1]

            if player1 and player2:
                # Create match
                self.game_counter += 1
                game_id = self.game_counter

                # Randomly assign colors
                import random
                if random.random() < 0.5:
                    white, black = player1, player2
                    white_handler, black_handler = data1['handler'], data2['handler']
                else:
                    white, black = player2, player1
                    white_handler, black_handler = data2['handler'], data1['handler']

                # Store game
                self.active_games[game_id] = {
                    'white': white,
                    'black': black,
                    'white_handler': white_handler,
                    'black_handler': black_handler,
                    'board_state': None,
                    'current_turn': 'white'
                }

                # Remove from queue
                del self.queue[player1]
                del self.queue[player2]
                
                # Notify both players
                white_handler.send(MSG_MATCH_FOUND, {
                    'game_id': game_id,
                    'opponent': black,
                    'color': 'white'
                })

                black_handler.send(MSG_MATCH_FOUND, {
                    'game_id': game_id,
                    'opponent': white,
                    'color': 'black'
                })
    
    def join_queue(self, username, handler):
        """Add a player to the matchmaking queue."""
        with self.lock:
            if username in self.queue:
                return False, "Already in queue"
            
            # Get player rating from database
            db = handler.db._load_db()
            rating = 1200  # Default rating
            if username in db.get('users', {}):
                # Calculate simple rating from wins/losses
                user_data = db['users'][username]
                wins = user_data.get('wins', 0)
                losses = user_data.get('losses', 0)
                draws = user_data.get('draws', 0)
                total = wins + losses + draws
                if total > 0:
                    rating = 1200 + ((wins - losses) / max(total, 1)) * 100
            
            self.queue[username] = {
                'rating': rating,
                'joined_time': time.time(),
                'handler': handler
            }
            
            return True, f"Joined queue (Rating: {int(rating)})"
    
    def leave_queue(self, username):
        """Remove a player from the matchmaking queue."""
        with self.lock:
            if username in self.queue:
                del self.queue[username]
                return True, "Left queue"
            return False, "Not in queue"
    
    def get_queue_status(self, username):
        """Get queue position for a player."""
        with self.lock:
            if username not in self.queue:
                return False, None

            position = sum(1 for p, d in self.queue.items()
                          if d['joined_time'] <= self.queue[username]['joined_time'])
            wait_time = time.time() - self.queue[username]['joined_time']

            return True, {
                'position': position,
                'wait_time': int(wait_time),
                'queued_players': len(self.queue)
            }

    def trigger_matchmaking(self, username):
        """Trigger an immediate matchmaking check for a player."""
        with self.lock:
            if username not in self.queue:
                return False, "Not in queue"
            
            # Try to find a match immediately
            if len(self.queue) < 2:
                return True, {"message": f"Waiting for opponents ({len(self.queue)} queued)"}
            
            # Sort by rating and find similar-rated opponent
            queued = sorted(self.queue.items(), key=lambda x: x[1]['rating'])
            max_elo_diff = 200
            
            for i in range(len(queued) - 1):
                p1_name, p1_data = queued[i]
                p2_name, p2_data = queued[i + 1]
                
                elo_diff = abs(p1_data['rating'] - p2_data['rating'])
                if elo_diff <= max_elo_diff and (p1_name == username or p2_name == username):
                    # Found a match! The background thread will handle it
                    return True, {"message": "Match found! Check your connection."}
            
            return True, {"message": f"No suitable opponent found yet ({len(self.queue)} queued)"}
    
    def get_game(self, game_id):
        """Get game info."""
        with self.lock:
            return self.active_games.get(game_id)
    
    def make_move(self, game_id, player, move):
        """Process a move in an active game."""
        with self.lock:
            game = self.active_games.get(game_id)
            if not game:
                return False, "Game not found"
            
            # Verify it's the player's turn
            expected_player = game['white'] if game['current_turn'] == 'white' else game['black']
            if player != expected_player:
                return False, "Not your turn"
            
            # Get the other player's handler
            if player == game['white']:
                game['current_turn'] = 'black'
                other_handler = game['black_handler']
            else:
                game['current_turn'] = 'white'
                other_handler = game['white_handler']
            
            # Forward move to opponent
            other_handler.send(MSG_GAME_MOVE, {
                'game_id': game_id,
                'move': move,
                'from_player': player
            })
            
            return True, "Move sent"
    
    def resign(self, game_id, player):
        """Handle resignation."""
        with self.lock:
            game = self.active_games.get(game_id)
            if not game:
                return None
            
            # Determine winner
            winner = game['black'] if player == game['white'] else game['white']
            
            # Notify both players
            game['white_handler'].send(MSG_GAME_RESIGN, {
                'game_id': game_id,
                'resigned_by': player,
                'winner': winner
            })
            game['black_handler'].send(MSG_GAME_RESIGN, {
                'game_id': game_id,
                'resigned_by': player,
                'winner': winner
            })
            
            # Remove game
            del self.active_games[game_id]
            
            return {'winner': winner, 'loser': player}
    
    def offer_draw(self, game_id, player):
        """Offer a draw to opponent."""
        with self.lock:
            game = self.active_games.get(game_id)
            if not game:
                return False, "Game not found"
            
            # Get opponent
            opponent = game['black'] if player == game['white'] else game['white']
            opponent_handler = game['black_handler'] if player == game['white'] else game['white_handler']
            
            # Send draw offer
            opponent_handler.send(MSG_GAME_DRAW_OFFER, {
                'game_id': game_id,
                'offered_by': player
            })
            
            return True, "Draw offered"
    
    def accept_draw(self, game_id, player):
        """Accept a draw offer."""
        with self.lock:
            game = self.active_games.get(game_id)
            if not game:
                return None
            
            # Notify both players
            game['white_handler'].send(MSG_GAME_DRAW_ACCEPT, {
                'game_id': game_id,
                'accepted_by': player,
                'result': 'draw'
            })
            game['black_handler'].send(MSG_GAME_DRAW_ACCEPT, {
                'game_id': game_id,
                'accepted_by': player,
                'result': 'draw'
            })
            
            # Remove game
            del self.active_games[game_id]
            
            return {'result': 'draw'}
    
    def send_chat(self, game_id, player, message):
        """Send chat message to opponent."""
        with self.lock:
            game = self.active_games.get(game_id)
            if not game:
                return False
            
            # Get opponent's handler
            opponent_handler = game['black_handler'] if player == game['white'] else game['white_handler']
            
            opponent_handler.send(MSG_GAME_CHAT, {
                'game_id': game_id,
                'from_player': player,
                'message': message
            })
            
            return True


# ════════════════════════════════════════════════════════════════════════
#  CLIENT HANDLER
# ════════════════════════════════════════════════════════════════════════
class ClientHandler:
    """Handles communication with a single client."""

    def __init__(self, conn, addr, db_manager, matchmaking_manager=None):
        self.conn = conn
        self.addr = addr
        self.db = db_manager
        self.matchmaking = matchmaking_manager
        self.logged_in_user = None
        self.pending = b''
        self.current_game_id = None
        # E2E encryption session keys
        self.session_key = None  # 32-byte AES key
        self.client_public = None  # Client's DH public key for session
        self.encryption_enabled = False
        self._nonce_counter = 0  # For CTR mode nonce

    def _derive_nonce(self):
        """Derive a unique nonce for each message (12 bytes for GCM)."""
        self._nonce_counter += 1
        # Pack counter as 8-byte big-endian, then pad to 12 bytes
        return b'\x00\x00\x00\x00' + struct.pack('>Q', self._nonce_counter)

    def _encrypt_message(self, plaintext: bytes) -> bytes:
        """Encrypt a message using session key."""
        if not self.encryption_enabled or self.session_key is None:
            return plaintext
        nonce = self._derive_nonce()
        ciphertext, tag = _gcm_encrypt(plaintext, self.session_key, nonce)
        # Prepend nonce to ciphertext
        return b'E' + nonce + ciphertext + tag

    def _decrypt_message(self, ciphertext: bytes) -> bytes:
        """Decrypt a message using session key."""
        if not self.encryption_enabled or self.session_key is None:
            return ciphertext
        if len(ciphertext) < 29:  # 1 (flag) + 12 (nonce) + 16 (tag)
            raise ValueError("Invalid encrypted message")
        if ciphertext[0:1] != b'E':
            raise ValueError("Invalid encryption flag")
        nonce = ciphertext[1:13]
        encrypted_data = ciphertext[13:-16]
        tag = ciphertext[-16:]
        return _gcm_decrypt(encrypted_data, self.session_key, nonce, tag)

    def send(self, msg_type, data='', success=True):
        """Send a message to the client (encrypted if session established)."""
        payload = json.dumps({
            'type': msg_type,
            'success': success,
            'data': data
        }).encode()

        # Encrypt if session is established (but not for key exchange messages)
        if self.encryption_enabled and self.session_key and msg_type not in [MSG_GET_SERVER_PUBLIC_KEY, MSG_SESSION_KEY_EXCHANGE]:
            payload = self._encrypt_message(payload)

        header = struct.pack('>I', len(payload))
        try:
            self.conn.sendall(header + payload)
            return True
        except (ConnectionResetError, BrokenPipeError, OSError) as e:
            # Client disconnected
            print(f"  [INFO] Send failed (client disconnected): {e}", flush=True)
            return False
        except Exception as e:
            print(f"  [ERROR] send error: {e}", flush=True)
            return False

    def recv(self, timeout=30.0):
        """Receive a message from the client (decrypt if session established)."""
        self.conn.settimeout(timeout)
        try:
            while True:
                # Need at least 4 bytes for header
                header_size = 4
                if len(self.pending) >= header_size:
                    # Check if this might be an encrypted payload
                    length = struct.unpack('>I', self.pending[:4])[0]
                    # Sanity check on length
                    if length > 10_000_000:  # 10MB max
                        self.pending = self.pending[1:]  # Skip byte and retry
                        continue
                    if len(self.pending) >= 4 + length:
                        payload = self.pending[4:4 + length]
                        self.pending = self.pending[4 + length:]
                        # Try to decrypt if encryption is enabled
                        if self.encryption_enabled and self.session_key and payload[0:1] == b'E':
                            payload = self._decrypt_message(payload)
                        return json.loads(payload.decode())

                chunk = self.conn.recv(4096)
                if not chunk:
                    # Client disconnected
                    return None
                self.pending += chunk
        except socket.timeout:
            return None
        except (ConnectionResetError, BrokenPipeError, OSError) as e:
            # Connection error - client disconnected unexpectedly
            print(f"  [INFO] Connection lost: {e}", flush=True)
            return None
        except Exception as e:
            print(f"  [ERROR] recv error: {e}", flush=True)
            return None

    def handle_register(self, data):
        """Handle user registration with E2E encryption."""
        # Check if data is encrypted
        if 'encrypted' in data and data['encrypted']:
            try:
                # Decrypt the credentials
                credentials = decrypt_credentials(data, ChessServer._server_private)
                username = credentials.get('username', '').strip()
                password = credentials.get('password', '')
                email = credentials.get('email', '').strip()
            except Exception as e:
                self.send(RESP_ERROR, "Decryption failed", False)
                return
        else:
            # Fallback to plaintext (for debugging)
            username = data.get('username', '').strip()
            password = data.get('password', '')
            email = data.get('email', '').strip()

        success, message = self.db.register_user(username, password, email)
        self.send(RESP_SUCCESS if success else RESP_ERROR, message, success)

    def handle_login(self, data):
        """Handle user login with E2E encryption."""
        # Check if data is encrypted
        if 'encrypted' in data and data['encrypted']:
            try:
                # Decrypt the credentials
                credentials = decrypt_credentials(data, ChessServer._server_private)
                username = credentials.get('username', '').strip()
                password = credentials.get('password', '')
            except Exception as e:
                print(f"  [DEBUG] Decryption failed: {e}", flush=True)
                self.send(RESP_ERROR, "Decryption failed", False)
                return
        else:
            # Fallback to plaintext (for debugging)
            username = data.get('username', '').strip()
            password = data.get('password', '')

        success, message = self.db.authenticate_user(username, password)
        if success:
            self.logged_in_user = username
            # Track connected client
            server = getattr(self, 'server', None)
            if server:
                server.connected_clients[username] = self
        self.send(RESP_SUCCESS if success else RESP_ERROR, message, success)

    def handle_auto_login(self, data):
        """Handle auto-login using stored password hash."""
        username = data.get('username', '').strip()
        password_hash = data.get('password_hash', '')

        success, message = self.db.authenticate_user_with_hash(username, password_hash)
        if success:
            self.logged_in_user = username
            # Track connected client
            server = getattr(self, 'server', None)
            if server:
                server.connected_clients[username] = self
        self.send(RESP_SUCCESS if success else RESP_ERROR, message, success)

    def handle_get_profile(self, data):
        """Handle profile request."""
        username = data.get('username', '').strip()
        
        if not username:
            username = self.logged_in_user
        
        if not username:
            self.send(RESP_ERROR, "Not logged in", False)
            return
        
        profile = self.db.get_user_profile(username)
        if profile:
            self.send(RESP_PROFILE, profile, True)
        else:
            self.send(RESP_ERROR, "User not found", False)
    
    def handle_save_game(self, data):
        """Handle game save request."""
        if not self.logged_in_user:
            self.send(RESP_ERROR, "Not logged in", False)
            return

        white = data.get('white', '')
        black = data.get('black', '')
        result = data.get('result', 'draw')
        moves = data.get('moves', [])
        duration = data.get('duration', 0)
        rated = data.get('rated', True)

        # Debug: Log the save request
        print(f"  [DEBUG] Saving game: {white} vs {black}, result={result}, rated={rated}")
        print(f"  [DEBUG] Logged in user: {self.logged_in_user}")

        # Verify that the logged-in user is one of the players
        if self.logged_in_user not in (white, black):
            print(f"  [DEBUG] Warning: Logged in user {self.logged_in_user} is not {white} or {black}")

        success, elo_changes = self.db.save_game(white, black, result, moves, duration, rated)
        
        if success and elo_changes:
            print(f"  [DEBUG] Game saved with ELO changes: {elo_changes}")
            self.send(RESP_SUCCESS, elo_changes, True)
        else:
            print(f"  [DEBUG] Game saved successfully={success}")
            self.send(RESP_SUCCESS if success else RESP_ERROR,
                      "Game saved" if success else "Failed to save game", success)
    
    def handle_list_users(self, data):
        """Handle user list request."""
        print(f"  [DEBUG] handle_list_users called with data: {data}", flush=True)
        try:
            users = self.db.list_users()
            print(f"  [DEBUG] Retrieved {len(users)} users: {users}", flush=True)
            self.send(RESP_USERS, users, True)
            print(f"  [DEBUG] Sent users list to client", flush=True)
        except Exception as e:
            print(f"  [ERROR] handle_list_users failed: {e}", flush=True)
            self.send(RESP_ERROR, str(e), False)

    def handle_leaderboard(self, data):
        """Handle leaderboard request."""
        limit = data.get('limit', 10)
        leaderboard = self.db.get_leaderboard(limit)
        self.send(RESP_LEADERBOARD, leaderboard, True)

    # ════════════════════════════════════════════════════════════════════
    #  MATCHMAKING HANDLERS
    # ════════════════════════════════════════════════════════════════════
    def handle_queue_join(self, data):
        """Handle joining matchmaking queue."""
        # Get username from data or fall back to logged_in_user
        username = data.get('username')
        if not username:
            username = self.logged_in_user

        if not username:
            self.send(RESP_ERROR, "Not logged in", False)
            return

        if not self.matchmaking:
            self.send(RESP_ERROR, "Matchmaking not available", False)
            return

        success, message = self.matchmaking.join_queue(username, self)
        self.send(RESP_QUEUED if success else RESP_ERROR, message, success)

    def handle_queue_leave(self, data):
        """Handle leaving matchmaking queue."""
        if not self.matchmaking:
            self.send(RESP_ERROR, "Matchmaking not available", False)
            return

        # Get username from data or fall back to logged_in_user
        username = data.get('username')
        if not username:
            username = self.logged_in_user

        if not username:
            self.send(RESP_ERROR, "Not logged in", False)
            return

        success, message = self.matchmaking.leave_queue(username)
        self.send(RESP_SUCCESS if success else RESP_ERROR, message, success)

    def handle_queue_status(self, data):
        """Handle queue status request."""
        if not self.matchmaking:
            self.send(RESP_ERROR, "Matchmaking not available", False)
            return

        # Get username from data or fall back to logged_in_user
        username = data.get('username')
        if not username:
            username = self.logged_in_user

        if not username:
            self.send(RESP_ERROR, "Not logged in", False)
            return

        # Check if client wants to trigger matchmaking
        if data.get('trigger'):
            success, result = self.matchmaking.trigger_matchmaking(username)
            if success:
                self.send(RESP_SUCCESS, result, True)
            else:
                self.send(RESP_ERROR, result, False)
        else:
            success, status = self.matchmaking.get_queue_status(username)
            if success:
                self.send(RESP_SUCCESS, status, True)
            else:
                self.send(RESP_ERROR, "Not in queue", False)
    
    def handle_game_move(self, data):
        """Handle a move in an active game."""
        if not self.logged_in_user or not self.matchmaking:
            self.send(RESP_ERROR, "Invalid request", False)
            return
        
        game_id = data.get('game_id')
        move = data.get('move')
        
        if game_id is None or not move:
            self.send(RESP_ERROR, "Invalid move data", False)
            return
        
        success, message = self.matchmaking.make_move(game_id, self.logged_in_user, move)
        self.send(RESP_SUCCESS if success else RESP_ERROR, message, success)
    
    def handle_game_resign(self, data):
        """Handle resignation."""
        if not self.logged_in_user or not self.matchmaking:
            return
        
        game_id = data.get('game_id')
        if game_id:
            result = self.matchmaking.resign(game_id, self.logged_in_user)
            if result:
                # Save game to database
                game = self.matchmaking.get_game(game_id)
                if game:
                    self.db.save_game(
                        game['white'], game['black'],
                        'black' if result['loser'] == 'white' else 'white',
                        [], 0
                    )
    
    def handle_game_draw_offer(self, data):
        """Handle draw offer."""
        if not self.logged_in_user or not self.matchmaking:
            return
        
        game_id = data.get('game_id')
        if game_id:
            self.matchmaking.offer_draw(game_id, self.logged_in_user)
    
    def handle_game_draw_accept(self, data):
        """Handle draw acceptance."""
        if not self.logged_in_user or not self.matchmaking:
            return
        
        game_id = data.get('game_id')
        if game_id:
            result = self.matchmaking.accept_draw(game_id, self.logged_in_user)
            if result:
                # Save draw to database
                game = self.matchmaking.get_game(game_id)
                if game:
                    self.db.save_game(game['white'], game['black'], 'draw', [], 0)
    
    def handle_game_chat(self, data):
        """Handle chat message."""
        if not self.logged_in_user or not self.matchmaking:
            return

        game_id = data.get('game_id')
        message = data.get('message', '')

        if game_id and message:
            self.matchmaking.send_chat(game_id, self.logged_in_user, message)

    # ════════════════════════════════════════════════════════════════════
    #  FRIEND SYSTEM HANDLERS
    # ════════════════════════════════════════════════════════════════════
    def handle_friend_request(self, data):
        """Handle sending a friend request."""
        if not self.logged_in_user:
            self.send(RESP_ERROR, "Not logged in", False)
            return

        recipient = data.get('recipient', '').strip()
        if not recipient:
            self.send(RESP_ERROR, "Recipient required", False)
            return

        success, message = self.db.send_friend_request(self.logged_in_user, recipient)
        self.send(RESP_SUCCESS if success else RESP_ERROR, message, success)

    def handle_friend_response(self, data):
        """Handle responding to a friend request."""
        if not self.logged_in_user:
            self.send(RESP_ERROR, "Not logged in", False)
            return

        sender = data.get('sender', '').strip()
        accept = data.get('accept', False)

        if not sender:
            self.send(RESP_ERROR, "Sender required", False)
            return

        success, message = self.db.respond_to_friend_request(sender, self.logged_in_user, accept)
        self.send(RESP_SUCCESS if success else RESP_ERROR, message, success)

        # Notify the sender
        if success and accept:
            # Find the sender's handler and notify
            server = getattr(self, 'server', None)
            if server and sender in server.connected_clients:
                server.connected_clients[sender].send(MSG_FRIEND_RESPONSE, {
                    'responder': self.logged_in_user,
                    'accepted': True
                })

    def handle_friend_list(self, data):
        """Handle getting friend list."""
        if not self.logged_in_user:
            self.send(RESP_ERROR, "Not logged in", False)
            return

        friends = self.db.get_friends(self.logged_in_user)
        # Get online status for each friend
        server = getattr(self, 'server', None)
        friend_status = []
        for friend in friends:
            friend_status.append({
                'username': friend,
                'online': friend in server.connected_clients if server else False
            })
        self.send(RESP_SUCCESS, {'friends': friend_status}, True)

    def handle_friend_remove(self, data):
        """Handle removing a friend."""
        if not self.logged_in_user:
            self.send(RESP_ERROR, "Not logged in", False)
            return

        friend = data.get('friend', '').strip()
        if not friend:
            self.send(RESP_ERROR, "Friend username required", False)
            return

        success, message = self.db.remove_friend(self.logged_in_user, friend)
        self.send(RESP_SUCCESS if success else RESP_ERROR, message, success)

    def handle_friend_requests_list(self, data):
        """Handle getting pending friend requests."""
        if not self.logged_in_user:
            self.send(RESP_ERROR, "Not logged in", False)
            return

        requests = self.db.get_friend_requests(self.logged_in_user)
        self.send(RESP_SUCCESS, {'requests': requests}, True)

    # ════════════════════════════════════════════════════════════════════
    #  MESSAGING SYSTEM HANDLERS
    # ════════════════════════════════════════════════════════════════════
    def handle_session_key_exchange(self, data):
        """Handle session key exchange for E2E encryption of all communications."""
        if not self.logged_in_user:
            self.send(RESP_ERROR, "Not logged in", False)
            return

        # Get client's public key
        client_public = data.get('client_public')
        if not client_public:
            self.send(RESP_ERROR, "Client public key required", False)
            return

        try:
            # Compute shared secret using server's private key and client's public key
            shared_secret = _dh_compute_shared_secret(ChessServer._server_private, client_public)

            # Store the session key
            self.session_key = shared_secret
            self.encryption_enabled = True
            self._nonce_counter = 0  # Reset nonce counter

            print(f"  [INFO] E2E encryption session established with {self.logged_in_user}", flush=True)

            # Send confirmation WITH server's public key (unencrypted so client can compute shared secret)
            # Temporarily disable encryption for this message
            old_encryption_state = self.encryption_enabled
            self.encryption_enabled = False
            self.send(RESP_SUCCESS, {
                'message': 'Session key exchange successful. All future communications are encrypted.',
                'server_public': ChessServer._server_public
            }, True)
            # Re-enable encryption
            self.encryption_enabled = old_encryption_state
        except Exception as e:
            print(f"  [ERROR] Session key exchange failed: {e}", flush=True)
            self.send(RESP_ERROR, "Session key exchange failed", False)

    def handle_key_exchange(self, data):
        """Handle key exchange for E2E encryption (legacy - use SESSION_KEY_EXCHANGE instead)."""
        # Redirect to session key exchange for backward compatibility
        self.handle_session_key_exchange(data)

    def handle_get_server_public_key(self, data):
        """Handle request for server's public key (for E2E encryption)."""
        # Send server's public key to client
        self.send(RESP_SUCCESS, {
            'server_public': ChessServer._server_public
        }, True)

    def handle_send_message(self, data):
        """Handle sending an encrypted message."""
        if not self.logged_in_user:
            self.send(RESP_ERROR, "Not logged in", False)
            return

        recipient = data.get('recipient', '').strip()
        encrypted_content = data.get('encrypted_content')
        iv = data.get('iv')
        tag = data.get('tag')

        if not recipient or not encrypted_content:
            self.send(RESP_ERROR, "Recipient and content required", False)
            return

        # Verify users are friends
        if not self.db.are_friends(self.logged_in_user, recipient):
            self.send(RESP_ERROR, "Can only message friends", False)
            return

        # Store the message
        success, result = self.db.store_message(
            self.logged_in_user, recipient, encrypted_content, iv, tag
        )
        
        if not success:
            self.send(RESP_ERROR, result, False)
            return

        # Try to notify the recipient if they're online
        server = getattr(self, 'server', None)
        if server and recipient in server.connected_clients:
            server.connected_clients[recipient].send(MSG_NEW_MESSAGE_NOTIFY, {
                'sender': self.logged_in_user,
                'message_id': result
            })

        self.send(RESP_SUCCESS, {'message_id': result}, True)

    def handle_get_messages(self, data):
        """Handle getting messages with a friend."""
        if not self.logged_in_user:
            self.send(RESP_ERROR, "Not logged in", False)
            return

        friend = data.get('friend', '').strip()
        since_id = data.get('since_id', 0)

        if not friend:
            self.send(RESP_ERROR, "Friend username required", False)
            return

        messages = self.db.get_messages(self.logged_in_user, friend, since_id)
        self.send(RESP_SUCCESS, {'messages': messages}, True)

    # ════════════════════════════════════════════════════════════════════
    #  CHALLENGE SYSTEM HANDLERS
    # ════════════════════════════════════════════════════════════════════
    def handle_challenge_send(self, data):
        """Handle sending a game challenge."""
        if not self.logged_in_user:
            self.send(RESP_ERROR, "Not logged in", False)
            return

        challenged = data.get('challenged', '').strip()
        color_choice = data.get('color_choice', 'random')
        rated = data.get('rated', True)

        if not challenged:
            self.send(RESP_ERROR, "Challenged user required", False)
            return

        success, result = self.db.send_challenge(
            self.logged_in_user, challenged, color_choice, rated
        )
        
        if not success:
            self.send(RESP_ERROR, result, False)
            return

        # Notify the challenged user
        server = getattr(self, 'server', None)
        if server and challenged in server.connected_clients:
            server.connected_clients[challenged].send(MSG_CHALLENGE_SEND, {
                'challenger': self.logged_in_user,
                'challenge_id': result,
                'color_choice': color_choice,
                'rated': rated
            })

        self.send(RESP_SUCCESS, {'challenge_id': result}, True)

    def handle_challenge_response(self, data):
        """Handle responding to a challenge."""
        if not self.logged_in_user:
            self.send(RESP_ERROR, "Not logged in", False)
            return

        challenger = data.get('challenger', '').strip()
        accept = data.get('accept', False)

        if not challenger:
            self.send(RESP_ERROR, "Challenger required", False)
            return

        success, result = self.db.respond_to_challenge(challenger, self.logged_in_user, accept)
        
        if not success:
            self.send(RESP_ERROR, result, False)
            return

        # Notify the challenger
        server = getattr(self, 'server', None)
        if server and challenger in server.connected_clients:
            server.connected_clients[challenger].send(MSG_CHALLENGE_RESPONSE, {
                'responder': self.logged_in_user,
                'accepted': accept,
                'details': result if accept else None
            })

        if accept:
            # Also send game start info to both players
            if server and challenger in server.connected_clients:
                server.connected_clients[challenger].send(MSG_GAME_START, {
                    'opponent': self.logged_in_user,
                    'color': result['challenger_color'],
                    'rated': result['rated'],
                    'challenge_id': result['challenge_id']
                })
            self.send(MSG_GAME_START, {
                'opponent': challenger,
                'color': result['challenged_color'],
                'rated': result['rated'],
                'challenge_id': result['challenge_id']
            })

        self.send(RESP_SUCCESS, result if accept else {'message': result}, True)

    def handle_challenge_list(self, data):
        """Handle getting pending challenges."""
        if not self.logged_in_user:
            self.send(RESP_ERROR, "Not logged in", False)
            return

        challenges = self.db.get_challenges(self.logged_in_user)
        self.send(RESP_SUCCESS, {'challenges': challenges}, True)

    def handle_challenge_cancel(self, data):
        """Handle cancelling a challenge."""
        if not self.logged_in_user:
            self.send(RESP_ERROR, "Not logged in", False)
            return

        challenged = data.get('challenged', '').strip()
        if not challenged:
            self.send(RESP_ERROR, "Challenged user required", False)
            return

        success, message = self.db.cancel_challenge(self.logged_in_user, challenged)
        self.send(RESP_SUCCESS if success else RESP_ERROR, message, success)

    def handle_request(self):
        """Main request handling loop."""
        print(f"  [INFO] Client connected: {self.addr[0]}:{self.addr[1]}", flush=True)

        # Main request handling loop
        while True:
            msg = self.recv(timeout=30.0)
            if not msg:
                break

            msg_type = msg.get('type', '')
            data = msg.get('data', {})

            if msg_type == MSG_REGISTER:
                self.handle_register(data)
            elif msg_type == MSG_LOGIN:
                self.handle_login(data)
            elif msg_type == MSG_AUTO_LOGIN:
                self.handle_auto_login(data)
            elif msg_type == MSG_LOGOUT:
                # Leave queue if in one
                if self.matchmaking and self.logged_in_user:
                    self.matchmaking.leave_queue(self.logged_in_user)
                # Remove from connected clients
                server = getattr(self, 'server', None)
                if server and self.logged_in_user in server.connected_clients:
                    del server.connected_clients[self.logged_in_user]
                self.logged_in_user = None
                self.send(RESP_SUCCESS, "Logged out", True)
            elif msg_type == MSG_GET_PROFILE:
                self.handle_get_profile(data)
            elif msg_type == MSG_SAVE_GAME:
                self.handle_save_game(data)
            elif msg_type == MSG_LIST_USERS:
                self.handle_list_users(data)
            elif msg_type == MSG_LEADERBOARD:
                self.handle_leaderboard(data)
            elif msg_type == MSG_PING:
                self.send(RESP_SUCCESS, "pong", True)
            # Matchmaking messages
            elif msg_type == MSG_QUEUE_JOIN:
                self.handle_queue_join(data)
            elif msg_type == MSG_QUEUE_LEAVE:
                self.handle_queue_leave(data)
            elif msg_type == MSG_QUEUE_STATUS:
                self.handle_queue_status(data)
            elif msg_type == MSG_GAME_MOVE:
                self.handle_game_move(data)
            elif msg_type == MSG_GAME_RESIGN:
                self.handle_game_resign(data)
            elif msg_type == MSG_GAME_DRAW_OFFER:
                self.handle_game_draw_offer(data)
            elif msg_type == MSG_GAME_DRAW_ACCEPT:
                self.handle_game_draw_accept(data)
            elif msg_type == MSG_GAME_CHAT:
                self.handle_game_chat(data)
            # Friend system messages
            elif msg_type == MSG_FRIEND_REQUEST:
                self.handle_friend_request(data)
            elif msg_type == MSG_FRIEND_RESPONSE:
                self.handle_friend_response(data)
            elif msg_type == MSG_FRIEND_LIST:
                self.handle_friend_list(data)
            elif msg_type == MSG_FRIEND_REMOVE:
                self.handle_friend_remove(data)
            elif msg_type == MSG_FRIEND_STATUS:
                self.handle_friend_requests_list(data)
            # Messaging system messages
            elif msg_type == MSG_KEY_EXCHANGE:
                self.handle_key_exchange(data)
            elif msg_type == MSG_SESSION_KEY_EXCHANGE:
                self.handle_session_key_exchange(data)
            elif msg_type == MSG_SEND_MESSAGE:
                self.handle_send_message(data)
            elif msg_type == MSG_GET_MESSAGES:
                self.handle_get_messages(data)
            # E2E Encryption
            elif msg_type == MSG_GET_SERVER_PUBLIC_KEY:
                self.handle_get_server_public_key(data)
            # Challenge system messages
            elif msg_type == MSG_CHALLENGE_SEND:
                self.handle_challenge_send(data)
            elif msg_type == MSG_CHALLENGE_RESPONSE:
                self.handle_challenge_response(data)
            elif msg_type == MSG_CHALLENGE_LIST:
                self.handle_challenge_list(data)
            elif msg_type == MSG_CHALLENGE_CANCEL:
                self.handle_challenge_cancel(data)
            else:
                self.send(RESP_ERROR, f"Unknown message type: {msg_type}", False)

    def close(self):
        """Close the connection."""
        try:
            # Leave queue if in one
            if self.matchmaking and self.logged_in_user:
                self.matchmaking.leave_queue(self.logged_in_user)
            # Properly shutdown the connection
            try:
                self.conn.shutdown(socket.SHUT_RDWR)
            except:
                pass
            self.conn.close()
        except Exception as e:
            print(f"  [DEBUG] close error: {e}", flush=True)


# ════════════════════════════════════════════════════════════════════════
#  CHESS SERVER
# ════════════════════════════════════════════════════════════════════════
class ChessServer:
    """Main chess server class."""
    
    # Server's long-term DH key pair (generated once at startup)
    _server_private, _server_public = _dh_generate_keypair()

    def __init__(self, host='0.0.0.0', port=SERVER_PORT):
        self.host = host
        self.port = port
        self.db_manager = DatabaseManager()
        self.matchmaking = MatchmakingManager()
        self.server_socket = None
        self.running = False
        self.clients = []
        self.connected_clients = {}  # username -> handler mapping for messaging
        self.cleanup_running = True

    def start(self):
        """Start the server."""
        self.server_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self.server_socket.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        self.server_socket.setsockopt(socket.SOL_SOCKET, socket.SO_KEEPALIVE, 1)

        try:
            self.server_socket.bind((self.host, self.port))
            self.server_socket.listen(5)
            self.running = True

            # Start matchmaking system
            self.matchmaking.start()

            # Start message cleanup thread
            cleanup_thread = threading.Thread(target=self._cleanup_loop, daemon=True)
            cleanup_thread.start()

            print("")
            print("╔══════════════════════════════════════════════════════════════╗")
            print("║                   CHESS SERVER STARTED                       ║")
            print("╠══════════════════════════════════════════════════════════════╣")
            print("║                                                              ║")
            print(f"║  Listening on: {self.host}:{self.port:<34}    ║")
            print(f"║  Database: {os.path.basename(DATABASE_FILE):<43}       ║")
            print("║  Matchmaking: Active                                         ║")
            print("║                                                              ║")
            print("║  Commands:                                                   ║")
            print("║    - Type 'users' to list all users                          ║")
            print("║    - Type 'queue' to show matchmaking queue                  ║")
            print("║    - Type 'quit' to stop the server                          ║")
            print("╚══════════════════════════════════════════════════════════════╝")
            print("")

            # Start command handler thread
            cmd_thread = threading.Thread(target=self._command_handler, daemon=True)
            cmd_thread.start()

            while self.running:
                try:
                    self.server_socket.settimeout(1.0)
                    conn, addr = self.server_socket.accept()
                    print(f"  [INFO] New connection from {addr[0]}:{addr[1]}", flush=True)

                    handler = ClientHandler(conn, addr, self.db_manager, self.matchmaking)
                    client_thread = threading.Thread(
                        target=self._handle_client,
                        args=(handler,),
                        daemon=True
                    )
                    client_thread.start()
                    self.clients.append(handler)

                except socket.timeout:
                    continue
                except Exception as e:
                    if self.running:
                        print(f"  [ERROR] Accept error: {e}")

        except Exception as e:
            print(f"  [ERROR] Server error: {e}")
        finally:
            self.stop()

    def _handle_client(self, handler):
        """Handle a client connection."""
        try:
            # Set server reference for notifications
            handler.server = self
            handler.handle_request()
        except Exception as e:
            print(f"  [ERROR] Client handler error: {e}", flush=True)
        finally:
            # Remove from connected clients
            if handler.logged_in_user and handler.logged_in_user in self.connected_clients:
                del self.connected_clients[handler.logged_in_user]
            handler.close()
            if handler in self.clients:
                self.clients.remove(handler)

    def _command_handler(self):
        """Handle server console commands."""
        while self.running:
            try:
                cmd = input("").strip().lower()
                if cmd == 'quit':
                    self.running = False
                elif cmd == 'users':
                    users = self.db_manager.list_users()
                    print(f"  [INFO] Registered users ({len(users)}): {', '.join(users) if users else 'None'}")
                elif cmd == 'queue':
                    with self.matchmaking.lock:
                        queue_count = len(self.matchmaking.queue)
                        games_count = len(self.matchmaking.active_games)
                    print(f"  [INFO] Matchmaking Queue: {queue_count} players waiting, {games_count} active games")
            except:
                pass

    def _cleanup_loop(self):
        """Background loop to cleanup expired messages."""
        while self.cleanup_running:
            time.sleep(3600)  # Check every hour
            try:
                deleted = self.db_manager.cleanup_expired_messages()
                if deleted > 0:
                    print(f"  [INFO] Cleaned up {deleted} expired messages", flush=True)
            except Exception as e:
                print(f"  [ERROR] Message cleanup failed: {e}", flush=True)

    def stop(self):
        """Stop the server."""
        self.running = False
        self.cleanup_running = False
        self.matchmaking.stop()
        for client in self.clients:
            client.close()
        if self.server_socket:
            self.server_socket.close()
        print("  [INFO] Server stopped.")


# ════════════════════════════════════════════════════════════════════════
#  CLIENT CONNECTION CLASS (for chess.py to use)
# ════════════════════════════════════════════════════════════════════════
class ChessClient:
    """Client connection for chess.py to communicate with the server."""
    
    def __init__(self, host='localhost', port=SERVER_PORT):
        self.host = host
        self.port = port
        self.sock = None
        self.logged_in_user = None
        self.pending = b''
    
    def connect(self):
        """Connect to the server."""
        try:
            self.sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            self.sock.settimeout(10.0)
            self.sock.connect((self.host, self.port))
            self.sock.settimeout(None)
            return True, "Connected to server"
        except Exception as e:
            return False, f"Connection failed: {e}"
    
    def disconnect(self):
        """Disconnect from the server."""
        self.logged_in_user = None
        if self.sock:
            try:
                self.sock.close()
            except:
                pass
            self.sock = None
    
    def send(self, msg_type, data=None):
        """Send a message to the server."""
        if not self.sock:
            return False
        
        payload = json.dumps({
            'type': msg_type,
            'data': data or {}
        }).encode()
        header = struct.pack('>I', len(payload))
        
        try:
            self.sock.sendall(header + payload)
            return True
        except:
            return False
    
    def recv(self, timeout=5.0):
        """Receive a response from the server."""
        if not self.sock:
            return None
        
        self.sock.settimeout(timeout)
        try:
            while True:
                if len(self.pending) >= 4:
                    length = struct.unpack('>I', self.pending[:4])[0]
                    if len(self.pending) >= 4 + length:
                        payload = self.pending[4:4 + length]
                        self.pending = self.pending[4 + length:]
                        return json.loads(payload.decode())
                chunk = self.sock.recv(4096)
                if not chunk:
                    return None
                self.pending += chunk
        except socket.timeout:
            return None
        except:
            return None
    
    def register(self, username, password, email):
        """Register a new account."""
        self.send(MSG_REGISTER, {
            'username': username,
            'password': password,
            'email': email
        })
        return self.recv()
    
    def login(self, username, password):
        """Login to an account."""
        self.send(MSG_LOGIN, {
            'username': username,
            'password': password
        })
        response = self.recv()
        if response and response.get('success'):
            self.logged_in_user = username
        return response
    
    def logout(self):
        """Logout from the account."""
        self.send(MSG_LOGOUT)
        response = self.recv()
        if response and response.get('success'):
            self.logged_in_user = None
        return response
    
    def get_profile(self, username=None):
        """Get a user's profile."""
        data = {'username': username} if username else {}
        self.send(MSG_GET_PROFILE, data)
        return self.recv()
    
    def save_game(self, white, black, result, moves, duration=0):
        """Save a game to history."""
        self.send(MSG_SAVE_GAME, {
            'white': white,
            'black': black,
            'result': result,
            'moves': moves,
            'duration': duration
        })
        return self.recv()
    
    def list_users(self):
        """Get list of all users."""
        self.send(MSG_LIST_USERS)
        return self.recv()

    # ════════════════════════════════════════════════════════════════════
    #  MATCHMAKING CLIENT METHODS
    # ════════════════════════════════════════════════════════════════════
    def join_queue(self):
        """Join the matchmaking queue."""
        self.send(MSG_QUEUE_JOIN)
        return self.recv()

    def leave_queue(self):
        """Leave the matchmaking queue."""
        self.send(MSG_QUEUE_LEAVE)
        return self.recv()

    def get_queue_status(self):
        """Get queue status."""
        self.send(MSG_QUEUE_STATUS)
        return self.recv()

    def send_move(self, game_id, move):
        """Send a move in an active game."""
        self.send(MSG_GAME_MOVE, {
            'game_id': game_id,
            'move': move
        })
        return self.recv()

    def resign_game(self, game_id):
        """Resign from a game."""
        self.send(MSG_GAME_RESIGN, {
            'game_id': game_id
        })

    def offer_draw(self, game_id):
        """Offer a draw to opponent."""
        self.send(MSG_GAME_DRAW_OFFER, {
            'game_id': game_id
        })

    def accept_draw(self, game_id):
        """Accept a draw offer."""
        self.send(MSG_GAME_DRAW_ACCEPT, {
            'game_id': game_id
        })

    def send_chat(self, game_id, message):
        """Send chat message to opponent."""
        self.send(MSG_GAME_CHAT, {
            'game_id': game_id,
            'message': message
        })

    # ════════════════════════════════════════════════════════════════════
    #  FRIEND SYSTEM CLIENT METHODS
    # ════════════════════════════════════════════════════════════════════
    def send_friend_request(self, recipient):
        """Send a friend request."""
        self.send(MSG_FRIEND_REQUEST, {'recipient': recipient})
        return self.recv()

    def respond_to_friend_request(self, sender, accept):
        """Respond to a friend request."""
        self.send(MSG_FRIEND_RESPONSE, {'sender': sender, 'accept': accept})
        return self.recv()

    def get_friend_list(self):
        """Get list of friends."""
        self.send(MSG_FRIEND_LIST)
        return self.recv()

    def remove_friend(self, friend):
        """Remove a friend."""
        self.send(MSG_FRIEND_REMOVE, {'friend': friend})
        return self.recv()

    def get_friend_requests(self):
        """Get pending friend requests."""
        self.send(MSG_FRIEND_STATUS)
        return self.recv()

    # ════════════════════════════════════════════════════════════════════
    #  MESSAGING SYSTEM CLIENT METHODS
    # ════════════════════════════════════════════════════════════════════
    def key_exchange(self, public_key, key_type='dh'):
        """Perform key exchange for E2E encryption."""
        self.send(MSG_KEY_EXCHANGE, {'public_key': public_key, 'key_type': key_type})
        return self.recv()

    def send_message(self, recipient, encrypted_content, iv, tag):
        """Send an encrypted message."""
        self.send(MSG_SEND_MESSAGE, {
            'recipient': recipient,
            'encrypted_content': encrypted_content,
            'iv': iv,
            'tag': tag
        })
        return self.recv()

    def get_messages(self, friend, since_id=0):
        """Get messages with a friend."""
        self.send(MSG_GET_MESSAGES, {'friend': friend, 'since_id': since_id})
        return self.recv()

    # ════════════════════════════════════════════════════════════════════
    #  CHALLENGE SYSTEM CLIENT METHODS
    # ════════════════════════════════════════════════════════════════════
    def send_challenge(self, challenged, color_choice='random', rated=True):
        """Send a game challenge."""
        self.send(MSG_CHALLENGE_SEND, {
            'challenged': challenged,
            'color_choice': color_choice,
            'rated': rated
        })
        return self.recv()

    def respond_to_challenge(self, challenger, accept):
        """Respond to a challenge."""
        self.send(MSG_CHALLENGE_RESPONSE, {'challenger': challenger, 'accept': accept})
        return self.recv()

    def get_challenges(self):
        """Get pending challenges."""
        self.send(MSG_CHALLENGE_LIST)
        return self.recv()

    def cancel_challenge(self, challenged):
        """Cancel a pending challenge."""
        self.send(MSG_CHALLENGE_CANCEL, {'challenged': challenged})
        return self.recv()


# ════════════════════════════════════════════════════════════════════════
#  ENTRY POINT
# ════════════════════════════════════════════════════════════════════════
def main():
    """Run the chess server."""
    server = ChessServer()
    try:
        server.start()
    except KeyboardInterrupt:
        print("\n  [INFO] Server interrupted by user.")
        server.stop()


if __name__ == '__main__':
    main()
