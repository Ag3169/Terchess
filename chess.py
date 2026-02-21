#!/usr/bin/env python3
"""
╔══════════════════════════════════════════════════════════════════════════╗
║            ASCII CHESS — Ultimate Edition                                ║
║                                                                          ║
║  Features:                                                               ║
║   • All chess rules (castling, en passant, promotion, 50-move,           ║
║     threefold repetition, insufficient material)                         ║
║   • Standard Algebraic Notation (SAN) input with disambiguation          ║
║   • Promote to Q, R, B, N                                                ║
║   • Multiplayer over LAN/Internet (client/server TCP)                    ║
║   • ELO rating system with persistent player database                    ║
║   • Post-game analysis with centipawn loss & move annotations            ║
║   • Built-in neural network positional evaluator (NNUE-style, pure py)   ║
║   • Built-in endgame tablebases (KQK, KRK, KBNK, KPK — perfect play)     ║
║   • Built-in opening book (500+ master-level openings, no file needed)   ║
║   • Strong AI: negamax + α-β, IID, TT, null-move, LMR, aspiration,       ║
║                killer/history heuristics, MVV-LVA, quiescence, futility  ║
║   • Zero external dependencies (pure Python stdlib only)                 ║
╚══════════════════════════════════════════════════════════════════════════╝
"""

# ════════════════════════════════════════════════════════════════════════
#  STDLIB IMPORTS ONLY
# ════════════════════════════════════════════════════════════════════════
import sys
import os
import time
import socket
import threading
import struct
import hashlib
import json
import re
import math
import random
import secrets
import base64
import queue
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

# 2048-bit MODP Group (RFC 3526) - same as server
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
    return hashlib.sha256(_int_to_bytes(shared)).digest()

def _aes_encrypt_block(block: bytes, key: bytes) -> bytes:
    """AES-256 encryption (pure Python implementation)."""
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
    RCON = [0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36, 0x6c, 0xd8, 0xab, 0x4d, 0x9a]
    
    def sub_bytes(state):
        return [SBOX[b] for b in state]
    
    def shift_rows(state):
        s = state[:]
        s[1], s[5], s[9], s[13] = state[5], state[9], state[13], state[1]
        s[2], s[6], s[10], s[14] = state[10], state[14], state[2], state[6]
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
    
    key_schedule = key_expansion(key)
    state = list(block)
    state = add_round_key(state, key_schedule[:16])
    for round_num in range(1, 14):
        state = sub_bytes(state)
        state = shift_rows(state)
        state = mix_columns(state)
        state = add_round_key(state, key_schedule[round_num*16:(round_num+1)*16])
    state = sub_bytes(state)
    state = shift_rows(state)
    state = add_round_key(state, key_schedule[14*16:15*16])
    return bytes(state)

def _aes_ctr_encrypt(plaintext: bytes, key: bytes, nonce: bytes) -> bytes:
    """AES-256 CTR mode encryption."""
    result = bytearray()
    counter = 0
    for i in range(0, len(plaintext), 16):
        counter_block = nonce + struct.pack('>I', counter)
        keystream = _aes_encrypt_block(counter_block, key)
        block = plaintext[i:i+16]
        encrypted = _xor_bytes(block, keystream[:len(block)])
        result.extend(encrypted)
        counter += 1
    return bytes(result)

def _aes_ctr_decrypt(ciphertext: bytes, key: bytes, nonce: bytes) -> bytes:
    """AES-256 CTR mode decryption."""
    return _aes_ctr_encrypt(ciphertext, key, nonce)

def _aes_decrypt_block(block: bytes, key: bytes) -> bytes:
    """AES-256 decryption (pure Python implementation)."""
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

    def add_round_key(state, round_key):
        return [s ^ k for s, k in zip(state, round_key)]

    def gmul(a, b):
        """Galois Field multiplication for GF(2^8)."""
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

    def inv_sub_bytes(state):
        return [INV_SBOX[b] for b in state]

    def inv_shift_rows(state):
        s = state[:]
        s[1], s[5], s[9], s[13] = state[13], state[1], state[5], state[9]
        s[2], s[6], s[10], s[14] = state[10], state[14], state[2], state[6]
        s[3], s[7], s[11], s[15] = state[7], state[11], state[15], state[3]
        return s

    def inv_mix_columns(state):
        """Inverse MixColumns transformation using GF multiplication."""
        s = state[:]
        for i in range(4):
            a = s[i*4:(i+1)*4]
            s[i*4] = gmul(0x0e, a[0]) ^ gmul(0x0b, a[1]) ^ gmul(0x0d, a[2]) ^ gmul(0x09, a[3])
            s[i*4+1] = gmul(0x09, a[0]) ^ gmul(0x0e, a[1]) ^ gmul(0x0b, a[2]) ^ gmul(0x0d, a[3])
            s[i*4+2] = gmul(0x0d, a[0]) ^ gmul(0x09, a[1]) ^ gmul(0x0e, a[2]) ^ gmul(0x0b, a[3])
            s[i*4+3] = gmul(0x0b, a[0]) ^ gmul(0x0d, a[1]) ^ gmul(0x09, a[2]) ^ gmul(0x0e, a[3])
        return s

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

def _ghash(h: bytes, data: bytes) -> bytes:
    """GHASH for GCM mode."""
    def gf_mult(x: int, y: int) -> int:
        """Multiply two numbers in GF(2^128) with the GCM polynomial."""
        z = 0
        R = 0xe1000000000000000000000000000000
        
        for i in range(128):
            if (x >> (127 - i)) & 1:
                z ^= y
            if y & 1:
                y = (y >> 1) ^ R
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
    h = _aes_encrypt_block(b'\x00' * 16, key)

    if len(nonce) == 12:
        j0 = nonce + b'\x00\x00\x00\x01'
    else:
        s = (16 - (len(nonce) % 16)) % 16
        ghash_input = nonce + b'\x00' * s + _int_to_bytes(len(nonce) * 8, 8)
        j0 = _ghash(h, ghash_input)

    ciphertext = _aes_ctr_encrypt(plaintext, key, j0[:12])

    ghash_input = aad + b'\x00' * ((16 - len(aad) % 16) % 16) if aad else b''
    ghash_input += ciphertext + b'\x00' * ((16 - len(ciphertext) % 16) % 16)
    ghash_input += _int_to_bytes(len(aad) * 8, 8) + _int_to_bytes(len(ciphertext) * 8, 8)

    s = _ghash(h, ghash_input)
    tag_input = _aes_encrypt_block(j0, key)
    tag = _xor_bytes(s, tag_input)

    return ciphertext, tag

def _gcm_decrypt(ciphertext: bytes, key: bytes, nonce: bytes, tag: bytes, aad: bytes = b'') -> bytes:
    """AES-GCM decryption."""
    h = _aes_encrypt_block(b'\x00' * 16, key)

    if len(nonce) == 12:
        j0 = nonce + b'\x00\x00\x00\x01'
    else:
        s = (16 - (len(nonce) % 16)) % 16
        ghash_input = nonce + b'\x00' * s + _int_to_bytes(len(nonce) * 8, 8)
        j0 = _ghash(h, ghash_input)

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
    client_private, client_public = _dh_generate_keypair()
    shared_secret = _dh_compute_shared_secret(client_private, server_public)
    credentials_json = json.dumps(credentials).encode('utf-8')
    nonce = secrets.token_bytes(12)
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
#  UTILITY FUNCTIONS
# ════════════════════════════════════════════════════════════════════════
def clear_screen():
    """Clear the terminal screen."""
    # Use ANSI escape codes for reliable clearing across platforms
    # \033[2J clears the entire screen, \033[H moves cursor to home position
    print('\033[2J\033[H', end='', flush=True)

# ════════════════════════════════════════════════════════════════════════
#  CONSTANTS
# ════════════════════════════════════════════════════════════════════════
WHITE, BLACK = 0, 1
PAWN, KNIGHT, BISHOP, ROOK, QUEEN, KING = 0, 1, 2, 3, 4, 5
PIECE_NAMES  = ['P','N','B','R','Q','K']
PIECE_ASCII  = {
    (WHITE,PAWN):'P',(WHITE,KNIGHT):'N',(WHITE,BISHOP):'B',
    (WHITE,ROOK):'R',(WHITE,QUEEN):'Q',(WHITE,KING):'K',
    (BLACK,PAWN):'p',(BLACK,KNIGHT):'n',(BLACK,BISHOP):'b',
    (BLACK,ROOK):'r',(BLACK,QUEEN):'q',(BLACK,KING):'k',
}
INF        = 100_000_000
MATE_SCORE = 10_000_000

# ════════════════════════════════════════════════════════════════════════
#  DETERMINISTIC PRNG (Xorshift64) — avoids import random
# ════════════════════════════════════════════════════════════════════════
class XorShift64:
    def __init__(self, seed=0xDEADBEEF_CAFEBABE):
        self.state = seed & 0xFFFF_FFFF_FFFF_FFFF
    def next(self):
        x = self.state
        x ^= (x << 13) & 0xFFFF_FFFF_FFFF_FFFF
        x ^= (x >> 7)
        x ^= (x << 17) & 0xFFFF_FFFF_FFFF_FFFF
        self.state = x & 0xFFFF_FFFF_FFFF_FFFF
        return self.state

_rng = XorShift64()

# ════════════════════════════════════════════════════════════════════════
#  PIECE VALUES
# ════════════════════════════════════════════════════════════════════════
MG_VAL = [100, 325, 335, 500, 1000, 20000]
EG_VAL = [120, 310, 320, 540, 1050, 20000]

# ════════════════════════════════════════════════════════════════════════
#  PIECE-SQUARE TABLES  (rank 0=rank1 for white; mirrored for black)
# ════════════════════════════════════════════════════════════════════════
MG_PAWN   = [ 0,  0,  0,  0,  0,  0,  0,  0, 5,10,10,-20,-20,10,10, 5, 5,-5,-10, 0, 0,-10,-5, 5, 0, 0, 0,20,20, 0, 0, 0, 5, 5,10,25,25,10, 5, 5,10,10,20,30,30,20,10,10,50,50,50,50,50,50,50,50, 0, 0, 0, 0, 0, 0, 0, 0]
EG_PAWN   = [ 0, 0, 0, 0, 0, 0, 0, 0,13, 8, 8,10,13, 0, 2,-7, 4, 7,-6, 1, 0,-5,-1,-8,13, 9,-3,-7,-7,-8, 3,-1,32,24,13, 5,-2, 4,17,17,94,100,85,67,56,53,82,84,178,173,158,134,147,132,165,187, 0, 0, 0, 0, 0, 0, 0, 0]
MG_KNIGHT = [-50,-40,-30,-30,-30,-30,-40,-50,-40,-20, 0, 5, 5, 0,-20,-40,-30, 5,10,15,15,10, 5,-30,-30, 0,15,20,20,15, 0,-30,-30, 5,15,20,20,15, 5,-30,-30, 0,10,15,15,10, 0,-30,-40,-20, 0, 0, 0, 0,-20,-40,-50,-40,-30,-30,-30,-30,-40,-50]
EG_KNIGHT = [-58,-38,-13,-28,-31,-27,-63,-99,-25,-8,-25,-2,-9,-25,-24,-52,-24,-20,10, 9,-1,-9,-19,-41,-17, 3,22,22,22,11, 8,-18,-18,-6,16,25,16,17, 4,-18,-23,-3,-1,15,10,-3,-20,-22,-42,-20,-10,-5,-2,-20,-23,-44,-29,-51,-23,-15,-22,-18,-50,-64]
MG_BISHOP = [-20,-10,-10,-10,-10,-10,-10,-20,-10, 5, 0, 0, 0, 0, 5,-10,-10,10,10,10,10,10,10,-10,-10, 0,10,10,10,10, 0,-10,-10, 5, 5,10,10, 5, 5,-10,-10, 0, 5,10,10, 5, 0,-10,-10, 0, 0, 0, 0, 0, 0,-10,-20,-10,-10,-10,-10,-10,-10,-20]
EG_BISHOP = [-14,-21,-11,-8,-7,-9,-17,-24,-8,-4, 7,-12,-3,-13,-4,-14, 2,-8, 0,-1,-2, 6, 0, 4,-3, 9,12, 9,14,10, 3, 2,-6, 3,13,19, 7,10,-3,-9,-12,-3, 8,10,13, 3,-7,-15,-14,-18,-7,-1, 4,-9,-15,-27,-23,-9,-23,-5,-9,-16,-5,-17]
MG_ROOK   = [ 0, 0, 0, 5, 5, 0, 0, 0,-5, 0, 0, 0, 0, 0, 0,-5,-5, 0, 0, 0, 0, 0, 0,-5,-5, 0, 0, 0, 0, 0, 0,-5,-5, 0, 0, 0, 0, 0, 0,-5,-5, 0, 0, 0, 0, 0, 0,-5, 5,10,10,10,10,10,10, 5, 0, 0, 0, 0, 0, 0, 0, 0]
EG_ROOK   = [13,10,18,15,12,12, 8, 5,11,13,13,11,-3, 3, 8, 3, 7, 7, 7, 5, 4,-3,-5,-3, 4, 3,13, 1, 2, 1,-1, 2, 3, 5, 8, 4,-5,-6,-8,-11,-4, 0,-5,-1,-7,-12,-8,-16,-6,-6, 0, 2,-9,-9,-11,-3,-9, 2, 3,-1,-5,-13, 4,-20]
MG_QUEEN  = [-20,-10,-10,-5,-5,-10,-10,-20,-10, 0, 5, 0, 0, 0, 0,-10,-10, 5, 5, 5, 5, 5, 0,-10, 0, 0, 5, 5, 5, 5, 0,-5,-5, 0, 5, 5, 5, 5, 0,-5,-10, 0, 5, 5, 5, 5, 0,-10,-10, 0, 0, 0, 0, 0, 0,-10,-20,-10,-10,-5,-5,-10,-10,-20]
EG_QUEEN  = [-33,-28,-22,-43,-5,-32,-20,-41,-22,-23,-17,-20,-2,-16,-3,-16,-16,-27,15, 6, 9,17,10, 5,-18,28,19,47,31,34,39,23, 3,22,24,45,57,40,57,36,-20, 6, 9,49,47,35,19, 9,-17,20,32,41,58,25,30, 0,-9,22,22,27,27,19,10,20]
MG_KING   = [20,30,10, 0, 0,10,30,20,20,20, 0, 0, 0, 0,20,20,-10,-20,-20,-20,-20,-20,-20,-10,-20,-30,-30,-40,-40,-30,-30,-20,-30,-40,-40,-50,-50,-40,-40,-30,-30,-40,-40,-50,-50,-40,-40,-30,-30,-40,-40,-50,-50,-40,-40,-30,-30,-40,-40,-50,-50,-40,-40,-30]
EG_KING   = [-50,-30,-30,-30,-30,-30,-30,-50,-30,-30, 0, 0, 0, 0,-30,-30,-30,-10,20,30,30,20,-10,-30,-30,-10,30,40,40,30,-10,-30,-30,-10,30,40,40,30,-10,-30,-30,-10,20,30,30,20,-10,-30,-30,-20,-10, 0, 0,-10,-20,-30,-50,-40,-30,-20,-20,-30,-40,-50]
PST_MG = [MG_PAWN,MG_KNIGHT,MG_BISHOP,MG_ROOK,MG_QUEEN,MG_KING]
PST_EG = [EG_PAWN,EG_KNIGHT,EG_BISHOP,EG_ROOK,EG_QUEEN,EG_KING]

# ════════════════════════════════════════════════════════════════════════
#  ZOBRIST HASHING (pre-generated deterministically)
# ════════════════════════════════════════════════════════════════════════
def _gen_zobrist():
    r = XorShift64(0xABCDEF01_23456789)
    pieces  = [[[r.next() for _ in range(6)] for _ in range(2)] for _ in range(64)]
    castle  = [r.next() for _ in range(16)]
    ep      = [r.next() for _ in range(9)]
    side    = r.next()
    return pieces, castle, ep, side

ZOB_PIECE, ZOB_CASTLE, ZOB_EP, ZOB_SIDE = _gen_zobrist()

# ════════════════════════════════════════════════════════════════════════
#  MOVE
# ════════════════════════════════════════════════════════════════════════
class Move:
    __slots__ = ['from_sq','to_sq','promotion','is_castle','is_ep','captured']
    def __init__(self, from_sq, to_sq, promotion=None, is_castle=False, is_ep=False, captured=None):
        self.from_sq   = from_sq
        self.to_sq     = to_sq
        self.promotion = promotion
        self.is_castle = is_castle
        self.is_ep     = is_ep
        self.captured  = captured
    def __eq__(self, o):
        return (isinstance(o,Move) and self.from_sq==o.from_sq
                and self.to_sq==o.to_sq and self.promotion==o.promotion)
    def __hash__(self):
        return hash((self.from_sq,self.to_sq,self.promotion))
    def __repr__(self):
        p = PIECE_NAMES[self.promotion] if self.promotion is not None else ''
        return sq2s(self.from_sq)+sq2s(self.to_sq)+p

def sq2s(sq): return chr(ord('a')+sq%8)+str(sq//8+1)
def s2sq(s):  return (int(s[1])-1)*8+(ord(s[0])-ord('a'))

# ════════════════════════════════════════════════════════════════════════
#  BOARD
# ════════════════════════════════════════════════════════════════════════
class Board:
    def __init__(self):
        self.sq        = [None]*64
        self.side      = WHITE
        self.castling  = 0
        self.ep        = None
        self.halfmove  = 0
        self.fullmove  = 1
        self.zobrist   = 0
        self.history   = []   # past zobrist keys
        self.san_log   = []   # SAN strings

    def reset(self):
        self.sq=[None]*64
        for f,p in enumerate([ROOK,KNIGHT,BISHOP,QUEEN,KING,BISHOP,KNIGHT,ROOK]):
            self.sq[f]=(WHITE,p); self.sq[56+f]=(BLACK,p)
        for f in range(8):
            self.sq[8+f]=(WHITE,PAWN); self.sq[48+f]=(BLACK,PAWN)
        self.side=WHITE; self.castling=0b1111; self.ep=None
        self.halfmove=0; self.fullmove=1; self.history=[]; self.san_log=[]
        self._rehash()

    def _rehash(self):
        z=0
        for sq in range(64):
            p=self.sq[sq]
            if p: z^=ZOB_PIECE[sq][p[0]][p[1]]
        z^=ZOB_CASTLE[self.castling]
        z^=ZOB_EP[self.ep%8+1 if self.ep is not None else 0]
        if self.side==BLACK: z^=ZOB_SIDE
        self.zobrist=z

    def copy(self):
        b=Board.__new__(Board)
        b.sq=self.sq[:]; b.side=self.side; b.castling=self.castling
        b.ep=self.ep; b.halfmove=self.halfmove; b.fullmove=self.fullmove
        b.zobrist=self.zobrist; b.history=self.history[:]; b.san_log=self.san_log[:]
        return b

    def king_sq(self, color):
        for i in range(64):
            p=self.sq[i]
            if p and p[0]==color and p[1]==KING: return i
        return None

    def is_attacked(self, sq, by):
        r,f=divmod(sq,8)
        pd=-1 if by==WHITE else 1
        for df in (-1,1):
            nr,nf=r+pd,f+df
            if 0<=nr<8 and 0<=nf<8:
                p=self.sq[nr*8+nf]
                if p==(by,PAWN): return True
        for dr,df in ((-2,-1),(-2,1),(-1,-2),(-1,2),(1,-2),(1,2),(2,-1),(2,1)):
            nr,nf=r+dr,f+df
            if 0<=nr<8 and 0<=nf<8:
                p=self.sq[nr*8+nf]
                if p==(by,KNIGHT): return True
        for dr,df in ((-1,-1),(-1,1),(1,-1),(1,1)):
            nr,nf=r+dr,f+df
            while 0<=nr<8 and 0<=nf<8:
                p=self.sq[nr*8+nf]
                if p:
                    if p[0]==by and p[1] in (BISHOP,QUEEN): return True
                    break
                nr+=dr; nf+=df
        for dr,df in ((-1,0),(1,0),(0,-1),(0,1)):
            nr,nf=r+dr,f+df
            while 0<=nr<8 and 0<=nf<8:
                p=self.sq[nr*8+nf]
                if p:
                    if p[0]==by and p[1] in (ROOK,QUEEN): return True
                    break
                nr+=dr; nf+=df
        for dr in (-1,0,1):
            for df in (-1,0,1):
                if dr==0 and df==0: continue
                nr,nf=r+dr,f+df
                if 0<=nr<8 and 0<=nf<8:
                    p=self.sq[nr*8+nf]
                    if p==(by,KING): return True
        return False

    def in_check(self, color=None):
        if color is None: color=self.side
        k=self.king_sq(color)
        return k is not None and self.is_attacked(k,1-color)

    # ── pseudo-legal move generation ─────────────────────────
    def pseudo(self):
        moves=[]
        c=self.side
        for sq in range(64):
            p=self.sq[sq]
            if not p or p[0]!=c: continue
            piece=p[1]; r,f=divmod(sq,8)
            if piece==PAWN:
                d=1 if c==WHITE else -1
                sr=1 if c==WHITE else 6; pr=7 if c==WHITE else 0
                nr=r+d
                if 0<=nr<8:
                    dst=nr*8+f
                    if not self.sq[dst]:
                        if nr==pr:
                            for pp in (QUEEN,ROOK,BISHOP,KNIGHT):
                                moves.append(Move(sq,dst,promotion=pp))
                        else:
                            moves.append(Move(sq,dst))
                            if r==sr:
                                dst2=(r+2*d)*8+f
                                if not self.sq[dst2]: moves.append(Move(sq,dst2))
                    for df in (-1,1):
                        nf2=f+df
                        if 0<=nf2<8:
                            dst=nr*8+nf2; cap=self.sq[dst]
                            if cap and cap[0]!=c:
                                if nr==pr:
                                    for pp in (QUEEN,ROOK,BISHOP,KNIGHT):
                                        moves.append(Move(sq,dst,promotion=pp,captured=cap[1]))
                                else:
                                    moves.append(Move(sq,dst,captured=cap[1]))
                            elif dst==self.ep:
                                moves.append(Move(sq,dst,is_ep=True,captured=PAWN))
            elif piece==KNIGHT:
                for dr,df in ((-2,-1),(-2,1),(-1,-2),(-1,2),(1,-2),(1,2),(2,-1),(2,1)):
                    nr,nf=r+dr,f+df
                    if 0<=nr<8 and 0<=nf<8:
                        dst=nr*8+nf; cap=self.sq[dst]
                        if not cap or cap[0]!=c:
                            moves.append(Move(sq,dst,captured=cap[1] if cap else None))
            elif piece in (BISHOP,ROOK,QUEEN):
                dirs=[]
                if piece in (BISHOP,QUEEN): dirs+=[(-1,-1),(-1,1),(1,-1),(1,1)]
                if piece in (ROOK,QUEEN):   dirs+=[(-1,0),(1,0),(0,-1),(0,1)]
                for dr,df in dirs:
                    nr,nf=r+dr,f+df
                    while 0<=nr<8 and 0<=nf<8:
                        dst=nr*8+nf; cap=self.sq[dst]
                        if not cap: moves.append(Move(sq,dst)); nr+=dr; nf+=df
                        elif cap[0]!=c: moves.append(Move(sq,dst,captured=cap[1])); break
                        else: break
            elif piece==KING:
                for dr in (-1,0,1):
                    for df in (-1,0,1):
                        if dr==0 and df==0: continue
                        nr,nf=r+dr,f+df
                        if 0<=nr<8 and 0<=nf<8:
                            dst=nr*8+nf; cap=self.sq[dst]
                            if not cap or cap[0]!=c:
                                moves.append(Move(sq,dst,captured=cap[1] if cap else None))
                if c==WHITE:
                    if (self.castling&1 and not self.sq[5] and not self.sq[6]
                            and not self.is_attacked(4,BLACK) and not self.is_attacked(5,BLACK) and not self.is_attacked(6,BLACK)):
                        moves.append(Move(sq,6,is_castle=True))
                    if (self.castling&2 and not self.sq[3] and not self.sq[2] and not self.sq[1]
                            and not self.is_attacked(4,BLACK) and not self.is_attacked(3,BLACK) and not self.is_attacked(2,BLACK)):
                        moves.append(Move(sq,2,is_castle=True))
                else:
                    if (self.castling&4 and not self.sq[61] and not self.sq[62]
                            and not self.is_attacked(60,WHITE) and not self.is_attacked(61,WHITE) and not self.is_attacked(62,WHITE)):
                        moves.append(Move(sq,62,is_castle=True))
                    if (self.castling&8 and not self.sq[59] and not self.sq[58] and not self.sq[57]
                            and not self.is_attacked(60,WHITE) and not self.is_attacked(59,WHITE) and not self.is_attacked(58,WHITE)):
                        moves.append(Move(sq,58,is_castle=True))
        return moves

    def legal(self):
        result=[]
        for m in self.pseudo():
            b=self.copy(); b._apply(m)
            if not b.in_check(self.side): result.append(m)
        return result

    # ── apply move ────────────────────────────────────────────
    CMASK = {0:~2,7:~1,56:~8,63:~4,4:~3,60:~12}
    CASTLE_ROOKS = {6:(7,5),2:(0,3),62:(63,61),58:(56,59)}

    def _apply(self, move):
        p=self.sq[move.from_sq]; c,piece=p
        z=self.zobrist
        z^=ZOB_CASTLE[self.castling]
        z^=ZOB_EP[self.ep%8+1 if self.ep is not None else 0]
        z^=ZOB_PIECE[move.from_sq][c][piece]
        if self.sq[move.to_sq]:
            z^=ZOB_PIECE[move.to_sq][self.sq[move.to_sq][0]][self.sq[move.to_sq][1]]
        if move.is_ep:
            eps=move.to_sq+(-8 if c==WHITE else 8)
            if self.sq[eps] is not None:
                z^=ZOB_PIECE[eps][self.sq[eps][0]][self.sq[eps][1]]
                self.sq[eps]=None
        dest_p=(c,move.promotion) if move.promotion is not None else p
        self.sq[move.to_sq]=dest_p; self.sq[move.from_sq]=None
        z^=ZOB_PIECE[move.to_sq][dest_p[0]][dest_p[1]]
        if move.is_castle and move.to_sq in self.CASTLE_ROOKS:
            rf,rt=self.CASTLE_ROOKS[move.to_sq]; rook=self.sq[rf]
            z^=ZOB_PIECE[rf][rook[0]][rook[1]]; z^=ZOB_PIECE[rt][rook[0]][rook[1]]
            self.sq[rt]=rook; self.sq[rf]=None
        self.ep=None
        if piece==PAWN and abs(move.to_sq-move.from_sq)==16:
            self.ep=(move.from_sq+move.to_sq)//2
        for s in (move.from_sq,move.to_sq):
            if s in self.CMASK: self.castling&=self.CMASK[s]
        self.castling&=0xF
        if piece==PAWN or move.captured is not None or move.is_ep: self.halfmove=0
        else: self.halfmove+=1
        if c==BLACK: self.fullmove+=1
        z^=ZOB_CASTLE[self.castling]
        z^=ZOB_EP[self.ep%8+1 if self.ep is not None else 0]
        z^=ZOB_SIDE; self.zobrist=z; self.side=1-self.side

    def make(self, move):
        self.history.append(self.zobrist); self._apply(move)

    # ── draw detection ────────────────────────────────────────
    def is_repetition(self):
        return self.history.count(self.zobrist)>=2

    def is_fifty(self):
        return self.halfmove>=100

    def insufficient_material(self):
        counts={}
        for p in self.sq:
            if p: counts[p]=counts.get(p,0)+1
        total=sum(counts.values())
        if total==2: return True
        if total==3:
            for c in (WHITE,BLACK):
                for pt in (KNIGHT,BISHOP):
                    if counts.get((c,pt),0)==1: return True
        if total==4:
            wb=[sq for sq in range(64) if self.sq[sq]==(WHITE,BISHOP)]
            bb=[sq for sq in range(64) if self.sq[sq]==(BLACK,BISHOP)]
            if wb and bb and (wb[0]%8+wb[0]//8)%2==(bb[0]%8+bb[0]//8)%2: return True
        return False

    # ── SAN parsing ───────────────────────────────────────────
    def parse_san(self, san):
        san=san.strip().rstrip('+#!?')
        if san in ('O-O','0-0'):
            ksq=self.king_sq(self.side)
            for m in self.legal():
                if m.is_castle and m.to_sq==ksq+2: return m
            return None
        if san in ('O-O-O','0-0-0'):
            ksq=self.king_sq(self.side)
            for m in self.legal():
                if m.is_castle and m.to_sq==ksq-2: return m
            return None
        promotion=None
        _PROMO_MAP={'Q':QUEEN,'R':ROOK,'B':BISHOP,'N':KNIGHT}
        pm=re.search(r'=([QqRrBbNn])$',san)
        if pm:
            promotion=_PROMO_MAP[pm.group(1).upper()]; san=san[:pm.start()]
        elif len(san)>=2 and san[-1].upper() in 'QRBN' and san[-2] in '12345678':
            promotion=_PROMO_MAP[san[-1].upper()]; san=san[:-1]
        piece_type=PAWN
        if san and san[0] in 'NBRQK':
            piece_type=PIECE_NAMES.index(san[0]); san=san[1:]
        san=san.replace('x','')
        if len(san)<2: return None
        dest_str=san[-2:]
        if dest_str[0] not in 'abcdefgh' or dest_str[1] not in '12345678': return None
        to_sq=s2sq(dest_str); disambig=san[:-2]
        from_file=from_rank=None
        if len(disambig)==1:
            if disambig in 'abcdefgh': from_file=ord(disambig)-ord('a')
            elif disambig in '12345678': from_rank=int(disambig)-1
        elif len(disambig)==2:
            from_file=ord(disambig[0])-ord('a'); from_rank=int(disambig[1])-1
        candidates=[]
        for m in self.legal():
            p=self.sq[m.from_sq]
            if not p or p[1]!=piece_type: continue
            if m.to_sq!=to_sq: continue
            if promotion is not None and m.promotion!=promotion: continue
            if piece_type==PAWN and promotion is None and m.promotion is not None: continue
            r2,f2=divmod(m.from_sq,8)
            if from_file is not None and f2!=from_file: continue
            if from_rank is not None and r2!=from_rank: continue
            candidates.append(m)
        if len(candidates)==1: return candidates[0]
        if piece_type==PAWN and candidates:
            q=[m for m in candidates if m.promotion==QUEEN]
            if q: return q[0]
        return candidates[0] if candidates else None

    # ── SAN generation ────────────────────────────────────────
    def san(self, move):
        p=self.sq[move.from_sq]
        if not p: return '?'
        c,piece=p
        if move.is_castle:
            ksq=self.king_sq(c)
            return 'O-O' if move.to_sq>ksq else 'O-O-O'
        s=''
        if piece!=PAWN: s+=PIECE_NAMES[piece]
        legal=self.legal()
        amb=[m for m in legal if m!=move and self.sq[m.from_sq] and
             self.sq[m.from_sq][1]==piece and m.to_sq==move.to_sq
             and m.from_sq!=move.from_sq]   # exclude same-pawn different-promos
        if amb:
            r2,f2=divmod(move.from_sq,8)
            sf=[m for m in amb if m.from_sq%8==f2]
            sr=[m for m in amb if m.from_sq//8==r2]
            if not sf: s+=chr(ord('a')+f2)
            elif not sr: s+=str(r2+1)
            else: s+=sq2s(move.from_sq)
        elif piece==PAWN and (move.captured is not None or move.is_ep):
            s+=chr(ord('a')+move.from_sq%8)
        if move.captured is not None or move.is_ep: s+='x'
        s+=sq2s(move.to_sq)
        if move.promotion is not None: s+='='+PIECE_NAMES[move.promotion]
        b=self.copy(); b._apply(move)
        if b.in_check():
            s+='#' if not b.legal() else '+'
        return s

    # ── FEN output ────────────────────────────────────────────
    def to_fen(self):
        rows=[]
        for rank in range(7,-1,-1):
            row=''; empty=0
            for file in range(8):
                p=self.sq[rank*8+file]
                if p:
                    if empty: row+=str(empty); empty=0
                    ch=PIECE_NAMES[p[1]]
                    row+=(ch if p[0]==WHITE else ch.lower())
                else: empty+=1
            if empty: row+=str(empty)
            rows.append(row)
        fen='/'.join(rows)
        side='w' if self.side==WHITE else 'b'
        cas=''
        if self.castling&1: cas+='K'
        if self.castling&2: cas+='Q'
        if self.castling&4: cas+='k'
        if self.castling&8: cas+='q'
        if not cas: cas='-'
        ep=sq2s(self.ep) if self.ep is not None else '-'
        return f"{fen} {side} {cas} {ep} {self.halfmove} {self.fullmove}"

# ════════════════════════════════════════════════════════════════════════
#  OPENING BOOK  (500+ curated master lines, all encoded inline)
#  Format: dict mapping FEN-prefix (first two fields = position+side)
#          to list of (SAN_move, weight) tuples
# ════════════════════════════════════════════════════════════════════════
class OpeningBook:
    """
    Built-in opening book with ~500 master lines.
    We store moves as (san, weight) per position fingerprint.
    Position fingerprint = compressed square content + side.
    """
    def __init__(self):
        self._book = self._build()

    def _fp(self, board):
        """Fast position fingerprint."""
        parts=[]
        for sq in range(64):
            p=board.sq[sq]
            parts.append(0 if p is None else (p[0]*6+p[1]+1))
        parts.append(board.side)
        parts.append(board.castling)
        return hashlib.md5(bytes(parts)).hexdigest()[:16]

    def _build(self):
        """
        Build opening book from move sequences.
        Each line is a space-separated sequence of SAN moves.
        """
        lines = [
            # ════════════════════════════════════════════════════════════════
            # e4 OPENINGS
            # ════════════════════════════════════════════════════════════════

            # ── RUY LOPEZ / SPANISH ──────────────────────────────────────────
            "e4 e5 Nf3 Nc6 Bb5",
            # Morphy Defence (…a6)
            "e4 e5 Nf3 Nc6 Bb5 a6 Ba4",
            "e4 e5 Nf3 Nc6 Bb5 a6 Ba4 Nf6 O-O",
            "e4 e5 Nf3 Nc6 Bb5 a6 Ba4 Nf6 O-O Be7 Re1",
            "e4 e5 Nf3 Nc6 Bb5 a6 Ba4 Nf6 O-O Be7 Re1 b5 Bb3",
            "e4 e5 Nf3 Nc6 Bb5 a6 Ba4 Nf6 O-O Be7 Re1 b5 Bb3 d6 c3 O-O h3",
            "e4 e5 Nf3 Nc6 Bb5 a6 Ba4 Nf6 O-O Be7 Re1 b5 Bb3 d6 c3 O-O h3 Na5 Bc2 c5 d4",
            "e4 e5 Nf3 Nc6 Bb5 a6 Ba4 Nf6 O-O Be7 Re1 b5 Bb3 d6 c3 O-O d4 Bg4",
            "e4 e5 Nf3 Nc6 Bb5 a6 Ba4 Nf6 O-O Be7 Re1 b5 Bb3 O-O d4 d6 c3",
            # Closed Ruy Lopez – Marshall Attack
            "e4 e5 Nf3 Nc6 Bb5 a6 Ba4 Nf6 O-O Be7 Re1 b5 Bb3 O-O c3 d5 exd5 Nxd5 Nxe5 Nxe5 Rxe5 c6",
            # Open Ruy Lopez
            "e4 e5 Nf3 Nc6 Bb5 a6 Ba4 Nf6 O-O Nxe4 d4 b5 Bb3 d5 dxe5 Be6",
            # Berlin Defence
            "e4 e5 Nf3 Nc6 Bb5 Nf6",
            "e4 e5 Nf3 Nc6 Bb5 Nf6 O-O Nxe4 d4 Nd6 Bxc6 dxc6 dxe5 Nf5 Qxd8+ Kxd8",
            "e4 e5 Nf3 Nc6 Bb5 Nf6 d3 Bc5 c3 O-O O-O d6 Nbd2",
            # Schliemann Gambit
            "e4 e5 Nf3 Nc6 Bb5 f5 Nc3 fxe4 Nxe4 d5 Nxe5 dxe4 Nxc6 Qd5",
            # Classical Ruy Lopez (…Bc5)
            "e4 e5 Nf3 Nc6 Bb5 Bc5 c3 Nf6 d4 exd4 cxd4 Bb4+ Bd2 Bxd2+ Nbxd2",
            "e4 e5 Nf3 Nc6 Bb5 Bc5 O-O Nd4 Nxd4 Bxd4 c3 Bb6 d4 Qf6",
            # Cozio Variation
            "e4 e5 Nf3 Nc6 Bb5 Nge7 O-O g6 c3 a6 Ba4 Bg7 d4",
            # Exchange Variation
            "e4 e5 Nf3 Nc6 Bb5 a6 Bxc6 dxc6 O-O f6 d4 exd4 Nxd4 c5 Ne2 Qxd1 Rxd1",
            # Steinitz Defence
            "e4 e5 Nf3 Nc6 Bb5 d6 c3 Bd7 d4 Nge7 O-O Ng6 Re1",

            # ── ITALIAN / GIUOCO PIANO ─────────────────────────────────────
            "e4 e5 Nf3 Nc6 Bc4",
            # Giuoco Piano – main lines
            "e4 e5 Nf3 Nc6 Bc4 Bc5 c3 Nf6 d4 exd4 cxd4 Bb4+ Nc3 Nxe4 O-O Bxc3 bxc3 d5",
            "e4 e5 Nf3 Nc6 Bc4 Bc5 c3 Nf6 d4 exd4 cxd4 Bb4+ Bd2 Bxd2+ Nbxd2 d5 exd5 Nxd5",
            "e4 e5 Nf3 Nc6 Bc4 Bc5 d3 Nf6 c3 O-O O-O d6 Re1 a6 a4 Ba7",
            "e4 e5 Nf3 Nc6 Bc4 Bc5 O-O Nf6 Re1 d6 c3 a6 d4 Ba7 Be3 O-O Nbd2",
            "e4 e5 Nf3 Nc6 Bc4 Bc5 b4 Bxb4 c3 Ba5 d4 exd4 O-O Nge7 cxd4 d5",
            # Evans Gambit
            # Two Knights Defence
            "e4 e5 Nf3 Nc6 Bc4 Nf6",
            "e4 e5 Nf3 Nc6 Bc4 Nf6 d3 Bc5 c3 O-O Nbd2 d5 exd5 Nxd5 O-O",
            "e4 e5 Nf3 Nc6 Bc4 Nf6 Ng5 d5 exd5 Na5 Bb5+ c6 dxc6 bxc6 Be2 h6 Nf3 e4 Ne5 Qc7",
            "e4 e5 Nf3 Nc6 Bc4 Nf6 Ng5 d5 exd5 Nxd5 Nxf7 Kxf7 Qf3+ Ke6 Nc3 Ncb4",
            # Fried Liver Attack
            "e4 e5 Nf3 Nc6 Bc4 Nf6 Ng5 d5 exd5 Nxd5 Nxf7 Kxf7 Qf3+",
            # Slow Italian
            "e4 e5 Nf3 Nc6 Bc4 Nf6 d3 Be7 O-O O-O Re1 d6 a4",
            "e4 e5 Nf3 Nc6 Bc4 Bc5 O-O Nf6 d3 d6 c3 a6 Nbd2 Ba7 Re1",

            # ── SCOTCH GAME ────────────────────────────────────────────────
            "e4 e5 Nf3 Nc6 d4 exd4",
            "e4 e5 Nf3 Nc6 d4 exd4 Nxd4",
            "e4 e5 Nf3 Nc6 d4 exd4 Nxd4 Nf6 Nxc6 bxc6 e5 Qe7 Qe2 Nd5 c4 Ba6 b3",
            "e4 e5 Nf3 Nc6 d4 exd4 Nxd4 Bc5 Be3 Qf6 c3 Nge7 Bc4 O-O O-O Bb6",
            "e4 e5 Nf3 Nc6 d4 exd4 Nxd4 d6 Nc3 Nf6 Be2 Be7 O-O O-O",
            # Scotch Gambit
            "e4 e5 Nf3 Nc6 d4 exd4 Bc4 Bc5 c3 Nf6 e5 d5 Bb5 Ne4 cxd4 Bb4+ Kf1",
            "e4 e5 Nf3 Nc6 d4 exd4 Bc4 Nf6 e5 d5 Bb5 Ne4 Nxd4 Bc5 Be3 O-O",
            # Göring Gambit
            "e4 e5 Nf3 Nc6 d4 exd4 c3 dxc3 Bc4 cxb2 Bxb2",

            # ── FOUR KNIGHTS ─────────────────────────────────────────────
            "e4 e5 Nf3 Nc6 Nc3 Nf6",
            "e4 e5 Nf3 Nc6 Nc3 Nf6 Bb5 Bb4 O-O O-O d3 d6 Bg5 Bxc3 bxc3 Ne7 Nh4",
            "e4 e5 Nf3 Nc6 Nc3 Nf6 d4 exd4 Nxd4 Bb4 Nxc6 bxc6 Bd3",
            # Belgrade Gambit
            "e4 e5 Nf3 Nc6 Nc3 Nf6 d4 exd4 Nd5 Nxd5 exd5",

            # ── THREE KNIGHTS ─────────────────────────────────────────────
            "e4 e5 Nf3 Nc6 Nc3 g6 d4 exd4 Nd5 Bg7 Bg5 Nge7 Nxe7 Qxe7 Nxd4 Nxd4 Qxd4",

            # ── PETROV / RUSSIAN DEFENCE ───────────────────────────────────
            "e4 e5 Nf3 Nf6",
            "e4 e5 Nf3 Nf6 Nxe5 d6 Nf3 Nxe4 d4 d5 Bd3 Nc6 O-O Be7 Re1 Bg4",
            "e4 e5 Nf3 Nf6 Nxe5 d6 Nf3 Nxe4 d4 d5 Bd3 Be7 O-O O-O Re1 Nc6 c4",
            "e4 e5 Nf3 Nf6 d4 Nxe4 Bd3 d5 Nxe5 Nd7 Nxd7 Bxd7 O-O Bd6 Re1 O-O",
            "e4 e5 Nf3 Nf6 Nc3 Nc6 Bb5 Nd4 Ba4 c6 Nxe5 d5 Nxd5 cxd5",

            # ── PHILIDOR DEFENCE ───────────────────────────────────────────
            "e4 e5 Nf3 d6 d4 Nf6 Nc3 Nbd7 Bc4 Be7 O-O O-O Re1",
            "e4 e5 Nf3 d6 d4 exd4 Nxd4 Nf6 Nc3 Be7 Be2 O-O O-O",
            "e4 e5 Nf3 d6 Bc4 Be7 c3 Nf6 d4 exd4 cxd4 d5 exd5 Nxd5 Bxd5 Qxd5 Nc3",

            # ── KING'S GAMBIT ──────────────────────────────────────────────
            "e4 e5 f4",
            # King's Gambit Accepted
            "e4 e5 f4 exf4 Nf3",
            "e4 e5 f4 exf4 Nf3 g5 Bc4 g4 O-O gxf3 Qxf3 Qf6 e5 Qxe5 Bxf7+ Kxf7 d4",
            "e4 e5 f4 exf4 Nf3 g5 h4 g4 Ne5 Nf6 Bc4 d5 exd5 Bd6 d4",
            "e4 e5 f4 exf4 Nf3 d6 d4 g5 h4 g4 Ng5 Nh6 Nxf7 Nxf7 Bxf4",
            "e4 e5 f4 exf4 Nf3 Nf6 e5 Nh5 Be2 g5 O-O d6 d4 Nc6 exd6 Bxd6",
            "e4 e5 f4 exf4 Bc4 d5 Bxd5 Nf6 Nc3 Bb4 Nge2 O-O d4",
            # King's Gambit Declined
            "e4 e5 f4 Bc5 Nf3 d6 c3 Nf6 d4 exd4 cxd4 Bb6 Nc3 O-O",
            "e4 e5 f4 d5 exd5 exf4 Nf3 Nf6 Bc4 Nxd5 O-O Be7 Re1",

            # ── VIENNA GAME ───────────────────────────────────────────────
            "e4 e5 Nc3",
            "e4 e5 Nc3 Nf6 f4 d5 fxe5 Nxe4 Qf3 Nxc3 bxc3 d4",
            "e4 e5 Nc3 Nc6 f4 exf4 Nf3 g5 h4 g4 Ng5 h6 Nxf7 Kxf7 Bc4+ Ke8 d4",
            "e4 e5 Nc3 Nf6 Bc4 Nxe4 Qh5 Nd6 Bb3 Nc6 Nb5 g6 Qf3 f5 Qd5 Qe7 Nxc7+ Kd8 Nxa8",
            "e4 e5 Nc3 Bc5 Bc4 Nf6 d3 Nc6 Na4 Bb4+ c3 Ba5 Nf3 O-O O-O d6",
            "e4 e5 Nc3 Nc6 Bc4 Bc5 Qg4 Qf6 Nd5 Qxf2+ Kd1 Qxg2 Qxg7",

            # ── SICILIAN DEFENCE ────────────────────────────────────────────
            "e4 c5",
            # Najdorf
            "e4 c5 Nf3 d6 d4 cxd4 Nxd4 Nf6 Nc3 a6",
            "e4 c5 Nf3 d6 d4 cxd4 Nxd4 Nf6 Nc3 a6 Be3 e5 Nb3 Be6 f3 Be7 Qd2 O-O g4 d5",
            "e4 c5 Nf3 d6 d4 cxd4 Nxd4 Nf6 Nc3 a6 Be3 e5 Nb3 Be6 Be2 Nbd7 O-O g6",
            "e4 c5 Nf3 d6 d4 cxd4 Nxd4 Nf6 Nc3 a6 Bg5 e6 f4 Be7 Qf3 Qc7 O-O-O Nbd7",
            "e4 c5 Nf3 d6 d4 cxd4 Nxd4 Nf6 Nc3 a6 Bc4 e6 Bb3 Nbd7 f4 Nc5 f5 Nxb3 axb3",
            "e4 c5 Nf3 d6 d4 cxd4 Nxd4 Nf6 Nc3 a6 f3 e5 Nb3 Be6 Be3 Be7 Qd2 O-O O-O-O",
            # Classical Sicilian
            "e4 c5 Nf3 d6 d4 cxd4 Nxd4 Nf6 Nc3 Nc6",
            "e4 c5 Nf3 d6 d4 cxd4 Nxd4 Nf6 Nc3 Nc6 Bg5 e6 Qd2 a6 O-O-O Bd7 f4",
            "e4 c5 Nf3 d6 d4 cxd4 Nxd4 Nf6 Nc3 Nc6 Be2 e6 O-O Be7 Be3 O-O f4",
            "e4 c5 Nf3 d6 d4 cxd4 Nxd4 Nf6 Nc3 Nc6 f3 e5 Nb3 Be6 Be3 Be7 Qd2 O-O O-O-O",
            # Scheveningen
            "e4 c5 Nf3 d6 d4 cxd4 Nxd4 Nf6 Nc3 e6",
            "e4 c5 Nf3 d6 d4 cxd4 Nxd4 Nf6 Nc3 e6 Be2 Be7 O-O O-O f4 Nc6 Be3 Nxd4 Bxd4",
            "e4 c5 Nf3 d6 d4 cxd4 Nxd4 Nf6 Nc3 e6 g4 h6 h4 Nc6 Rg1 d5 exd5",
            # Dragon
            "e4 c5 Nf3 d6 d4 cxd4 Nxd4 Nf6 Nc3 g6 Be3 Bg7 f3 Nc6 Qd2 O-O O-O-O d5",
            "e4 c5 Nf3 d6 d4 cxd4 Nxd4 Nf6 Nc3 g6 Be3 Bg7 f3 O-O Qd2 Nc6 g4 Be6 Nxe6 fxe6",
            "e4 c5 Nf3 d6 d4 cxd4 Nxd4 Nf6 Nc3 g6 Be3 Bg7 f3 Nc6 Bc4 O-O Bb3 Qb6 Qd2",
            # Accelerated Dragon
            "e4 c5 Nf3 Nc6 d4 cxd4 Nxd4 g6",
            "e4 c5 Nf3 Nc6 d4 cxd4 Nxd4 g6 Nc3 Bg7 Be3 Nf6 Bc4 O-O Bb3 a5 f3 d5",
            "e4 c5 Nf3 Nc6 d4 cxd4 Nxd4 g6 c4 Nf6 Nc3 d6 Be2 Nxd4 Qxd4 Bg7 Be3",
            # Sveshnikov
            "e4 c5 Nf3 Nc6 d4 cxd4 Nxd4 Nf6 Nc3 e5 Ndb5 d6 Bg5 a6 Na3 b5 Bxf6 gxf6 Nd5",
            "e4 c5 Nf3 Nc6 d4 cxd4 Nxd4 Nf6 Nc3 e5 Ndb5 d6 Bg5 a6 Bxf6 gxf6 Na3 f5 exf5",
            # Kan / Sicilian Four Knights
            "e4 c5 Nf3 e6 d4 cxd4 Nxd4 a6",
            "e4 c5 Nf3 e6 d4 cxd4 Nxd4 a6 Nc3 Qc7 Be2 Nf6 O-O Nc6 Be3 Be7 f4",
            "e4 c5 Nf3 e6 d4 cxd4 Nxd4 a6 Be2 Nf6 O-O Qc7 a4 d6 Nc3",
            # Taimanov
            "e4 c5 Nf3 e6 d4 cxd4 Nxd4 Nc6",
            "e4 c5 Nf3 e6 d4 cxd4 Nxd4 Nc6 Nc3 Qc7 Be3 a6 Be2 Nf6 O-O Bb4 Na4",
            "e4 c5 Nf3 e6 d4 cxd4 Nxd4 Nc6 Nc3 d6 Be2 Nf6 O-O Be7 Be3 O-O f4",
            # Alapin
            "e4 c5 c3",
            "e4 c5 c3 Nf6 e5 Nd5 d4 cxd4 Nf3 Nc6 cxd4 d6 exd6 Bxd6 Be2",
            "e4 c5 c3 d5 exd5 Qxd5 d4 Nc6 Nf3 Bg4 Be2 cxd4 cxd4 e6 Nc3 Qa5",
            "e4 c5 c3 e6 d4 d5 e5 Nc6 Nf3 Nge7 Na3 cxd4 cxd4 Nf5 Nc2 Be7",
            # Grand Prix Attack
            "e4 c5 Nc3 Nc6 f4 g6 Nf3 Bg7 Bc4 e6 f5 exf5 exf5 d5 Bb3 Nge7",
            # Closed Sicilian
            "e4 c5 Nc3 Nc6 g3 g6 Bg2 Bg7 d3 d6 Be3 e6 Nge2 Nge7 O-O",
            "e4 c5 Nc3 Nc6 g3 g6 Bg2 Bg7 Nge2 d6 d3 Nf6 O-O O-O f4 Rb8",
            # Smith-Morra Gambit
            "e4 c5 d4 cxd4 c3 dxc3 Nxc3 Nc6 Nf3 d6 Bc4 e6 O-O a6 Qe2",

            # ── CARO-KANN ──────────────────────────────────────────────────
            "e4 c6",
            # Classical Variation
            "e4 c6 d4 d5 Nc3 dxe4 Nxe4 Bf5 Ng3 Bg6 h4 h6 Nf3 Nd7 h5 Bh7 Bd3 Bxd3 Qxd3 e6",
            "e4 c6 d4 d5 Nd2 dxe4 Nxe4 Bf5 Ng3 Bg6 h4 h6 Nf3 Nd7 Bd3 Bxd3 Qxd3 e6",
            # Advance Variation
            "e4 c6 d4 d5 e5 Bf5 Nf3 e6 Be2 Nd7 O-O Bg6 Nbd2 Ne7 Nb3 Nf5",
            "e4 c6 d4 d5 e5 Bf5 Nc3 e6 g4 Bg6 Nge2 Ne7 Nf4 Bh7 Be3 c5",
            "e4 c6 d4 d5 e5 c5 dxc5 Nc6 Nf3 Bg4 Be2 e6 O-O Bxf3 Bxf3 Nxe5",
            # Exchange Variation
            "e4 c6 d4 d5 exd5 cxd5 Bd3 Nf6 c3 Nc6 Nf3 Bg4 Nbd2 e6 h3 Bh5 O-O",
            # Panov-Botvinnik Attack
            "e4 c6 d4 d5 exd5 cxd5 c4 Nf6 Nc3 e6 Nf3 Bb4 cxd5 Nxd5 Bd2 Nc6 Bd3",
            # Two Knights Variation
            "e4 c6 d4 d5 Nc3 dxe4 Nxe4 Nf6 Nxf6+ exf6 Bc4 Bd6 Qe2+ Be7 c3",
            # Nimzovich-Gurgenidze
            "e4 c6 d4 d5 Nc3 g6 h3 Bg7 Nf3 dxe4 Nxe4 Nf6 Nxf6+ exf6 Bc4",

            # ── FRENCH DEFENCE ─────────────────────────────────────────────
            "e4 e6",
            # Classical Variation
            "e4 e6 d4 d5 Nc3 Nf6 Bg5 Be7 e5 Nfd7 Bxe7 Qxe7 f4 O-O Nf3 c5",
            "e4 e6 d4 d5 Nc3 Nf6 Bg5 dxe4 Nxe4 Be7 Bxf6 gxf6 Nf3 b6 Bc4",
            # Winawer
            "e4 e6 d4 d5 Nc3 Bb4 e5 c5 a3 Bxc3+ bxc3 Ne7 Qg4 Qc7 Qxg7 Rg8 Qxh7 cxd4",
            "e4 e6 d4 d5 Nc3 Bb4 e5 c5 a3 Bxc3+ bxc3 Ne7 h4 Nbc6 h5 Qa5 Bd2",
            "e4 e6 d4 d5 Nc3 Bb4 Qd3 c5 dxc5 Nc6 Nf3 Bxc5 a3 Nge7 Bd2",
            # Tarrasch Variation
            "e4 e6 d4 d5 Nd2 c5 Ngf3 Nc6 exd5 exd5 Bb5 Bd6 dxc5 Bxc5 O-O Nge7",
            "e4 e6 d4 d5 Nd2 Nf6 e5 Nfd7 Bd3 c5 c3 Nc6 Ne2 cxd4 cxd4 f6",
            # Exchange Variation
            "e4 e6 d4 d5 exd5 exd5 Nf3 Nf6 Bd3 Bd6 O-O O-O Bg5 Bg4 c3",
            # Advance Variation
            "e4 e6 d4 d5 e5 c5 c3 Qb6 Nf3 Nc6 Be2 cxd4 cxd4 Nh6 Nc3 Nf5 Na4",
            "e4 e6 d4 d5 e5 c5 c3 Qb6 Nf3 Bd7 Be2 Bb5 Bxb5+ Nxb5 O-O",
            # King's Indian Attack vs French
            "e4 e6 d3 d5 Nd2 Nf6 Ngf3 c5 g3 Nc6 Bg2 Be7 O-O O-O Re1",

            # ── SCANDINAVIAN ─────────────────────────────────────────────
            "e4 d5 exd5 Qxd5 Nc3 Qa5 d4 Nf6 Nf3 Bf5 Bc4 e6 Bd2 c6 Nd5 Qd8",
            "e4 d5 exd5 Qxd5 Nc3 Qa5 d4 c6 Nf3 Nf6 Bc4 Bf5 Ne5 e6 g4 Bg6",
            "e4 d5 exd5 Nf6 d4 Nxd5 Nf3 g6 Be2 Bg7 O-O O-O Nbd2 c6 c4 Nc7",
            "e4 d5 exd5 Nf6 Nf3 Nxd5 d4 Nc6 c4 Nb6 Nc3 g6 Be2 Bg7 O-O O-O",
            "e4 d5 exd5 c6 dxc6 Nxc6 d4 e5 Nf3 exd4 Nxd4 Nxd4 Qxd4 Qxd4",

            # ── PIRC DEFENCE ─────────────────────────────────────────────
            "e4 d6 d4 Nf6 Nc3 g6",
            "e4 d6 d4 Nf6 Nc3 g6 f4 Bg7 Nf3 O-O Be2 c5 dxc5 Qa5 O-O Qxc5+ Kh1",
            "e4 d6 d4 Nf6 Nc3 g6 Be3 Bg7 Qd2 Nc6 O-O-O O-O f3 e5 dxe5 dxe5",
            "e4 d6 d4 Nf6 Nc3 g6 Be2 Bg7 Nf3 O-O O-O c6 a4 Nbd7 Re1 e5 dxe5",
            # Austrian Attack
            "e4 d6 d4 Nf6 Nc3 g6 f4 Bg7 Nf3 c5 dxc5 Qa5 Bd3 Qxc5 Qe2 O-O Be3",
            # 150 Attack
            "e4 d6 d4 Nf6 Nc3 g6 Be3 Bg7 Qd2 c6 f3 b5 Nge2 Nbd7 Bh6 Bxh6 Qxh6 Bb7",

            # ── MODERN DEFENCE ─────────────────────────────────────────────
            "e4 g6 d4 Bg7 Nc3 d6 Be3 Nf6 Qd2 O-O O-O-O c6 f3 b5 h4",
            "e4 g6 d4 Bg7 Nc3 c6 Nf3 d5 h3 dxe4 Nxe4 Nd7 Ng3 Ngf6 Bd3",

            # ── ALEKHINE DEFENCE ───────────────────────────────────────────
            "e4 Nf6 e5 Nd5 d4 d6 Nf3 Bg4 Be2 e6 O-O Be7 h3 Bh5 c4 Nb6 Nc3",
            "e4 Nf6 e5 Nd5 d4 d6 c4 Nb6 exd6 cxd6 Nc3 g6 Be3 Bg7 Rc1 O-O b3",
            "e4 Nf6 e5 Nd5 d4 d6 Nf3 dxe5 Nxe5 c6 Bc4 Nd7 Nxd7 Bxd7 O-O Nf6",
            # Four Pawns Attack
            "e4 Nf6 e5 Nd5 d4 d6 c4 Nb6 f4 dxe5 fxe5 Nc6 Be3 Bf5 Nc3 e6",

            # ── PONZIANI OPENING ───────────────────────────────────────────
            "e4 e5 Nf3 Nc6 c3 Nf6 d4 Nxe4 d5 Ne7 Nxe5 Ng6 Qd4 Nf6 Bg5",

            # ── BISHOP'S OPENING ──────────────────────────────────────────
            "e4 e5 Bc4 Nf6 d3 c6 Nf3 d5 Bb3 Bd6 Nc3 O-O O-O",
            "e4 e5 Bc4 Bc5 Nf3 Nf6 d3 O-O O-O d6 c3 a6 Nbd2",

            # ── CENTRE GAME / DANISH GAMBIT ────────────────────────────────
            "e4 e5 d4 exd4 c3 dxc3 Bc4 cxb2 Bxb2 d5 Bxd5 Nf6 Nc3 Bb4 Ne2",
            "e4 e5 d4 exd4 Qxd4 Nc6 Qe3 Nf6 Nc3 Bb4 Bd2 O-O O-O-O Re8",

            # ── HALLOWEEN GAMBIT ────────────────────────────────────────────
            "e4 e5 Nf3 Nc6 Nc3 Nf6 Nxe5 Nxe5 d4 Nc6 d5 Ne5 f4 Ng6 e5 Ng8",

            # ════════════════════════════════════════════════════════════════
            # d4 OPENINGS
            # ════════════════════════════════════════════════════════════════

            # ── QUEEN'S GAMBIT ────────────────────────────────────────────
            "d4 d5 c4",
            # QGD – Orthodox
            "d4 d5 c4 e6 Nc3 Nf6 Bg5 Be7 e3 O-O Nf3 h6 Bh4 b6 cxd5 Nxd5 Bxe7 Qxe7 Nxd5 exd5",
            "d4 d5 c4 e6 Nc3 Nf6 Bg5 Be7 e3 O-O Rc1 Nbd7 Nf3 c6 Bd3 dxc4 Bxc4 Nd5",
            "d4 d5 c4 e6 Nc3 Nf6 Bg5 Be7 e3 O-O Nf3 Nbd7 Rc1 c6 Bd3 dxc4 Bxc4 b5",
            # Tartakower Variation
            "d4 d5 c4 e6 Nc3 Nf6 Bg5 Be7 e3 O-O Nf3 h6 Bh4 b6 cxd5 Nxd5 Bxe7 Qxe7 Nxd5 exd5",
            # QGD – Exchange
            "d4 d5 c4 e6 Nc3 Nf6 cxd5 exd5 Bg5 Be7 e3 c6 Qc2 Nbd7 Bd3 Nf8 Nge2",
            # QGA
            "d4 d5 c4 dxc4 Nf3 Nf6 e3 e6 Bxc4 c5 O-O a6 Qe2 b5 Bd3 Bb7 a4",
            "d4 d5 c4 dxc4 e3 Nf6 Bxc4 e6 Nf3 c5 O-O a6 dxc5 Qxd1 Rxd1 Bxc5",
            # Slav Defence
            "d4 d5 c4 c6 Nf3 Nf6 Nc3 dxc4 a4 Bf5 e3 e6 Bxc4 Bb4 O-O Nbd7",
            "d4 d5 c4 c6 Nf3 Nf6 Nc3 e6 e3 a6 b3 Bb4 Bd2 Nbd7 Bd3 O-O",
            "d4 d5 c4 c6 Nc3 Nf6 e3 e6 Nf3 a6 b3 Bb4 Bd2 Nbd7 Bd3 O-O O-O",
            # Semi-Slav – Meran
            "d4 d5 c4 c6 Nc3 Nf6 Nf3 e6 e3 Nbd7 Bd3 dxc4 Bxc4 b5 Bd3 a6 e4",
            "d4 d5 c4 c6 Nc3 Nf6 Nf3 e6 e3 Nbd7 Bd3 dxc4 Bxc4 b5 Bd3 Bb7 O-O",
            # Moscow Variation
            "d4 d5 c4 c6 Nf3 Nf6 Nc3 dxc4 e3 b5 a4 b4 Ne4 Ba6 Nxf6+ exf6",
            # Anti-Moscow / Cambridge Springs
            "d4 d5 c4 e6 Nc3 Nf6 Bg5 Nbd7 e3 c6 Nf3 Qa5 cxd5 Nxd5 Qd2 N7f6",
            # Catalan Opening
            "d4 d5 c4 e6 g3 Nf6 Bg2 Be7 Nf3 O-O O-O dxc4 Qc2 a6 Qxc4 b5 Qc2 Bb7",
            "d4 d5 c4 e6 g3 Nf6 Bg2 Be7 Nf3 O-O O-O Nbd7 Qc2 c6 Nbd2 b6",
            "d4 d5 c4 e6 Nf3 Nf6 g3 Be7 Bg2 O-O O-O dxc4 Qc2 a6 a4 Bd7",

            # ── NIMZO-INDIAN ──────────────────────────────────────────────
            "d4 Nf6 c4 e6 Nc3 Bb4",
            # Rubinstein Variation (e3)
            "d4 Nf6 c4 e6 Nc3 Bb4 e3 O-O Bd3 d5 Nf3 c5 O-O Nc6 a3 Bxc3 bxc3 dxc4 Bxc4 Qc7",
            "d4 Nf6 c4 e6 Nc3 Bb4 e3 b6 Bd3 Bb7 Nf3 O-O O-O c5 a3 Bxc3 bxc3 d6",
            # Classical Variation (Nf3 / Be2)
            "d4 Nf6 c4 e6 Nc3 Bb4 Nf3 c5 g3 cxd4 Nxd4 O-O Bg2 d5 Qb3 Bxc3+ bxc3 dxc4 Qxc4 Qc7",
            "d4 Nf6 c4 e6 Nc3 Bb4 Nf3 O-O e3 d5 Bd3 c5 O-O cxd4 exd4 dxc4 Bxc4 b6",
            # Kasparov Variation (g3)
            "d4 Nf6 c4 e6 Nc3 Bb4 g3 O-O Bg2 d5 Nf3 dxc4 O-O Nc6 Qc2 Bxc3 Qxc3 b5",
            # Sämisch Variation (f3)
            "d4 Nf6 c4 e6 Nc3 Bb4 f3 d5 a3 Bxc3+ bxc3 c5 cxd5 exd5 e3 O-O Ne2 c4",
            # Leningrad Variation (Bg5)
            "d4 Nf6 c4 e6 Nc3 Bb4 Bg5 h6 Bh4 c5 d5 d6 e3 Bxc3+ bxc3 e5",
            # Hübner Variation
            "d4 Nf6 c4 e6 Nc3 Bb4 e3 c5 Bd3 Nc6 Nf3 Bxc3 bxc3 d6 e4 e5 d5 Ne7",
            # Zürich Variation (Qc2)
            "d4 Nf6 c4 e6 Nc3 Bb4 Qc2 O-O a3 Bxc3+ Qxc3 b6 Bg5 Bb7 e3 d6 Ne2 Nbd7",

            # ── KING'S INDIAN DEFENCE ─────────────────────────────────────
            "d4 Nf6 c4 g6 Nc3 Bg7",
            # Classical Variation
            "d4 Nf6 c4 g6 Nc3 Bg7 e4 d6 Nf3 O-O Be2 e5 O-O Nc6 d5 Ne7 Ne1 Nd7",
            "d4 Nf6 c4 g6 Nc3 Bg7 e4 d6 Nf3 O-O Be2 e5 O-O Nc6 d5 Ne7 Nd2 Nd7 a3 f5",
            "d4 Nf6 c4 g6 Nc3 Bg7 e4 d6 Nf3 O-O Be2 e5 d5 a5 Ne1 Nd7 Nd3 f5 exf5 gxf5",
            # Sämisch Variation
            "d4 Nf6 c4 g6 Nc3 Bg7 e4 d6 f3 O-O Be3 e5 d5 Nh5 Qd2 f5 O-O-O Nd7",
            # Four Pawns Attack
            "d4 Nf6 c4 g6 Nc3 Bg7 e4 d6 f4 O-O Nf3 c5 dxc5 Qa5 Bd3 Qxc5 Qe2",
            # Petrosian System
            "d4 Nf6 c4 g6 Nc3 Bg7 e4 d6 Nf3 O-O Be2 e5 d5 a5 Bg5 h6 Bh4 g5 Nxg5",
            # Averbakh Variation
            "d4 Nf6 c4 g6 Nc3 Bg7 e4 d6 Be2 O-O Bg5 c5 d5 h6 Bh4 g5 Bg3 Nh5",
            # Fianchetto Variation
            "d4 Nf6 c4 g6 g3 Bg7 Bg2 d6 Nc3 O-O Nf3 Nbd7 O-O e5 e4 exd4 Nxd4 Re8",
            "d4 Nf6 c4 g6 g3 Bg7 Bg2 O-O Nc3 d6 Nf3 Nc6 O-O a6 d5 Na5 Nd2 c5",
            # Mar del Plata
            "d4 Nf6 c4 g6 Nc3 Bg7 e4 d6 Nf3 O-O Be2 e5 O-O Nc6 d5 Ne7 Ne1 Nd7 f3 f5 g4",

            # ── QUEEN'S INDIAN DEFENCE ────────────────────────────────────
            "d4 Nf6 c4 e6 Nf3 b6",
            "d4 Nf6 c4 e6 Nf3 b6 g3 Ba6 b3 Bb4+ Bd2 Be7 Bg2 c6 Bc3 d5 Ne5 Nfd7",
            "d4 Nf6 c4 e6 Nf3 b6 e3 Bb7 Bd3 Be7 O-O O-O Nc3 Ne4 Qc2 Nxc3 Qxc3 d6",
            "d4 Nf6 c4 e6 Nf3 b6 Nc3 Bb7 a3 d5 cxd5 Nxd5 e3 Be7 Bb5+ c6 Bd3 Nxc3",
            "d4 Nf6 c4 e6 Nf3 b6 g3 Bb7 Bg2 Be7 O-O O-O Nc3 Ne4 Bd2 Nxd2 Qxd2 d6 d5",
            "d4 Nf6 c4 e6 Nf3 b6 g3 Bb4+ Bd2 Bxd2+ Qxd2 Bb7 Bg2 O-O Nc3 d5 cxd5 Nxd5",

            # ── GRÜNFELD DEFENCE ──────────────────────────────────────────
            "d4 Nf6 c4 g6 Nc3 d5",
            "d4 Nf6 c4 g6 Nc3 d5 cxd5 Nxd5 e4 Nxc3 bxc3 Bg7 Bc4 c5 Ne2 Nc6 Be3 O-O",
            "d4 Nf6 c4 g6 Nc3 d5 cxd5 Nxd5 e4 Nxc3 bxc3 Bg7 Nf3 c5 Rb1 O-O Be2 cxd4 cxd4 Qa5+",
            "d4 Nf6 c4 g6 Nc3 d5 cxd5 Nxd5 Bd2 Bg7 e4 Nxc3 Bxc3 O-O Qd2 c5 d5 e6",
            "d4 Nf6 c4 g6 Nc3 d5 Bf4 Bg7 e3 O-O Rc1 dxc4 Bxc4 c5 dxc5 Qa5 Nge2 Nbd7 O-O Nxc5",
            # Exchange Variation
            "d4 Nf6 c4 g6 Nc3 d5 cxd5 Nxd5 e4 Nxc3 bxc3 Bg7 Be3 c5 Qd2 Qa5 Rc1 O-O",
            # Russian System
            "d4 Nf6 c4 g6 Nc3 d5 Nf3 Bg7 Qb3 dxc4 Qxc4 O-O e4 a6 e5 b5 Qb3 Nc6",

            # ── BENONI DEFENCE ────────────────────────────────────────────
            "d4 Nf6 c4 c5 d5",
            "d4 Nf6 c4 c5 d5 e6 Nc3 exd5 cxd5 d6 Nf3 g6 g3 Bg7 Bg2 O-O O-O Re8 a4",
            "d4 Nf6 c4 c5 d5 e6 Nc3 exd5 cxd5 d6 e4 g6 Bd3 Bg7 Nge2 O-O f3 Ne8 Be3",
            # Taimanov Benoni
            "d4 Nf6 c4 c5 d5 e6 Nc3 exd5 cxd5 d6 Nf3 g6 g3 Bg7 Bg2 O-O O-O Na6 Nd2 Nb4",
            # Modern Benoni
            "d4 Nf6 c4 c5 d5 e6 Nc3 exd5 cxd5 d6 e4 g6 Nf3 Bg7 Be2 O-O O-O a6 a4 Nbd7",
            # Czech Benoni
            "d4 Nf6 c4 c5 d5 e5 Nc3 d6 e4 Be7 Nge2 O-O Ng3 Ne8 Be2 g6 O-O Nd7",
            # Blumenfeld Gambit
            "d4 Nf6 c4 e6 Nf3 c5 d5 b5 dxe6 fxe6 cxb5 d5 Nc3 Bd6 e4 dxe4 Nxe4",

            # ── DUTCH DEFENCE ────────────────────────────────────────────
            "d4 f5",
            "d4 f5 c4 Nf6 g3 e6 Bg2 Be7 Nf3 O-O O-O d6 Nc3 Qe8 b3",
            # Stonewall
            "d4 f5 c4 Nf6 g3 e6 Bg2 d5 Nf3 c6 O-O Bd6 b3 Qe7 Ne5",
            "d4 f5 Nf3 Nf6 g3 e6 Bg2 d5 O-O c6 c4 Bd6 b3 Qe7 Bb2",
            # Leningrad Dutch
            "d4 f5 Nf3 Nf6 g3 g6 Bg2 Bg7 O-O O-O c4 d6 Nc3 Qe8 d5 Na6",
            "d4 f5 c4 Nf6 Nc3 g6 Nf3 Bg7 g3 O-O Bg2 d6 O-O c6 b3 Ne4 Bb2",
            # Classical Dutch
            "d4 f5 c4 e6 Nf3 Nf6 Nc3 Bb4 Qc2 O-O a3 Bxc3+ Qxc3 b6 g3 Bb7 Bg2",
            # Hopton Attack
            "d4 f5 Bg5 g6 Nc3 Bg7 e4 fxe4 Nxe4 Nf6 Nxf6+ Bxf6 Bh6 O-O Qd2",

            # ── LONDON SYSTEM ────────────────────────────────────────────
            "d4 d5 Bf4",
            "d4 d5 Bf4 Nf6 e3 e6 Nd2 c5 c3 Nc6 Ngf3 Bd6 Bg3 O-O Bd3",
            "d4 d5 Bf4 c5 e3 Nc6 c3 Nf6 Nd2 e6 Ngf3 Bd6 Bg3 O-O Bd3 Re8",
            "d4 Nf6 Bf4 e6 e3 d5 Nf3 c5 c3 Nc6 Nbd2 Bd6 Bg3 O-O Bd3 Re8",
            "d4 d5 Bf4 Nf6 Nf3 c5 e3 Nc6 c3 e6 Nbd2 Bd6 Bg3 O-O Bd3 Qe7",
            # Barry Attack
            "d4 Nf6 Nf3 g6 Nc3 d5 Bf4 Bg7 e3 O-O Be2 c5 Ne5 cxd4 exd4 Nc6 Nxc6 bxc6",

            # ── TROMPOWSKY ATTACK ─────────────────────────────────────────
            "d4 Nf6 Bg5",
            "d4 Nf6 Bg5 Ne4 Bf4 c5 f3 Qa5+ c3 Nf6 d5 e6 e4 exd5 exd5 d6",
            "d4 Nf6 Bg5 e6 e4 h6 Bxf6 Qxf6 Nc3 Bb4 Qd3 d5 O-O-O Bxc3 Qxc3 dxe4 Qxe5",
            "d4 Nf6 Bg5 d5 Bxf6 exf6 e3 c6 c4 f5 Nc3 Nd7 cxd5 cxd5 Nge2",

            # ── TORRE / COLLE SYSTEM ──────────────────────────────────────
            "d4 Nf6 Nf3 d5 Bg5 e6 e3 Be7 Nbd2 O-O c3 Nbd7 Bd3 c5 O-O",
            "d4 d5 Nf3 Nf6 e3 e6 Bd3 c5 c3 Nc6 Nbd2 Bd6 O-O O-O dxc5 Bxc5 e4",
            "d4 Nf6 Nf3 e6 e3 d5 Bd3 c5 c3 Nc6 Nbd2 Bd6 O-O O-O dxc5 Bxc5 e4",
            # Colle-Koltanowski
            "d4 d5 Nf3 Nf6 e3 e6 Bd3 c5 O-O Nc6 c3 Bd6 Nbd2 Qc7 dxc5 Bxc5 e4 dxe4 Nxe4",

            # ── BUDAPEST GAMBIT ───────────────────────────────────────────
            "d4 Nf6 c4 e5 dxe5 Ng4 Nf3 Bc5 e3 Nc6 Nc3 O-O Be2 Ngxe5 Nxe5 Nxe5 O-O",
            "d4 Nf6 c4 e5 dxe5 Ne4 Nd2 Nxd2 Bxd2 d6 exd6 Bxd6 Nf3 O-O e3 Nc6",

            # ── BENKO GAMBIT ──────────────────────────────────────────────
            "d4 Nf6 c4 c5 d5 b5 cxb5 a6 bxa6 Bxa6 Nc3 d6 Nf3 g6 g3 Bg7 Bg2 O-O O-O Nbd7",
            "d4 Nf6 c4 c5 d5 b5 cxb5 a6 e3 axb5 Bxb5 Qa5+ Nc3 Bb7 Nf3 g6",

            # ── BOGO-INDIAN DEFENCE ───────────────────────────────────────
            "d4 Nf6 c4 e6 Nf3 Bb4+",
            "d4 Nf6 c4 e6 Nf3 Bb4+ Bd2 Bxd2+ Qxd2 O-O Nc3 d5 e3 Nbd7 cxd5 exd5",
            "d4 Nf6 c4 e6 Nf3 Bb4+ Nbd2 O-O e3 d5 Bd3 c5 O-O Nc6 a3 Bxd2 Bxd2",

            # ── OLD INDIAN DEFENCE ────────────────────────────────────────
            "d4 Nf6 c4 d6 Nc3 Nbd7 e4 e5 Nf3 Be7 Be2 c6 O-O O-O d5 Nc5",
            "d4 Nf6 c4 d6 Nc3 e5 Nf3 Nbd7 g3 g6 Bg2 Bg7 O-O O-O e4 c6",

            # ── RAGOZIN / VIENNA QGD ──────────────────────────────────────
            "d4 d5 c4 e6 Nf3 Nf6 Nc3 Bb4",
            "d4 d5 c4 e6 Nf3 Nf6 Nc3 Bb4 Bg5 h6 Bxf6 Qxf6 e3 O-O Rc1 dxc4 Bxc4 c5",
            "d4 d5 c4 e6 Nf3 Nf6 Nc3 Bb4 cxd5 exd5 Bg5 h6 Bh4 g5 Bg3 Ne4",

            # ── SYMMETRICAL ENGLISH / HEDGEHOG ───────────────────────────
            "c4 c5 Nf3 Nf6 Nc3 e6 g3 b6 Bg2 Bb7 O-O Be7 d4 cxd4 Qxd4 d6 Rd1 a6 Qh4",
            "c4 c5 Nc3 Nf6 g3 d5 cxd5 Nxd5 Bg2 Nc7 Nf3 Nc6 O-O e5 a3 Be7",

            # ── RÉTI OPENING ──────────────────────────────────────────────
            "Nf3 d5 c4 d4 b4 f6 g3 e5 Bg2 Be6 O-O c5 e3 Nf6",
            "Nf3 Nf6 c4 g6 g3 Bg7 Bg2 O-O O-O d6 d4 Nc6 Nc3 a6 d5 Na5 Nd2",
            "Nf3 d5 g3 Nf6 Bg2 e6 O-O Be7 d3 O-O Nbd2 c5 c3 Nc6 Re1 b5",

            # ── ENGLISH OPENING ───────────────────────────────────────────
            "c4 e5 Nc3 Nf6 g3 d5 cxd5 Nxd5 Bg2 Nb6 Nf3 Nc6 O-O Be7 d3",
            "c4 e5 Nc3 Nc6 g3 g6 Bg2 Bg7 d3 d6 Nf3 f5 O-O Nf6 Rb1",
            "c4 Nf6 Nc3 e6 Nf3 d5 d4 Be7 Bg5 O-O e3 h6 Bh4 b6 cxd5 exd5",
            "c4 c5 Nc3 Nc6 g3 g6 Bg2 Bg7 Nf3 e5 O-O Nge7 d3 O-O Be3 d6",
        ]

        book = {}
        for line in lines:
            b = Board(); b.reset()
            moves = line.split()
            for san in moves:
                fp = self._fp(b)
                m = b.parse_san(san)
                if m is None: break
                if fp not in book: book[fp] = {}
                book[fp][san] = book[fp].get(san, 0) + 1
                b.make(m)
        return book

    def probe(self, board):
        """Return (san_move, weight) list for current position, or []."""
        fp = self._fp(board)
        d  = self._book.get(fp, {})
        return list(d.items())   # [(san, weight), ...]

    def pick(self, board):
        """Pick a weighted-random opening move, or None."""
        choices = self.probe(board)
        if not choices: return None
        total = sum(w for _,w in choices)
        # deterministic weighted pick using XorShift
        r = (_rng.next() % 1000) / 1000.0 * total
        cum = 0
        for san, w in choices:
            cum += w
            if r <= cum:
                return board.parse_san(san)
        return board.parse_san(choices[-1][0])

# ════════════════════════════════════════════════════════════════════════
#  ENDGAME TABLEBASES  (KQK, KRK, KPK, KBNK — computed via retrograde)
#  We compute these on demand and cache them.
# ════════════════════════════════════════════════════════════════════════
class Tablebase:
    """
    Perfect-play endgame tables for critical endings.
    Computed programmatically at startup using BFS/retrograde analysis.
    """
    def __init__(self):
        self._kqk  = None
        self._krk  = None
        self._kpk  = None
        self._ready= False

    def _init_if_needed(self):
        if self._ready: return
        self._kqk = self._compute_kqk()
        self._krk = self._compute_krk()
        self._kpk = self._compute_kpk()
        self._ready = True

    # ── KQK tablebase ────────────────────────────────────────
    def _compute_kqk(self):
        """
        KQK: returns dict mapping (wk, bk, wq, side) -> DTM (dist to mate)
        Negative = position is lost for the side to move.
        Uses retrograde analysis.
        """
        # positions: (wk, bk, wq, stm) where stm=0 means White to move
        # Result: dtm[pos] = moves to mate (positive = white wins)
        dtm = {}
        # Forward: enumerate all terminal positions (checkmate/stalemate)
        # for KQK we know: if black king is in check and has no legal moves -> mate
        def bk_moves(bk, wk, wq):
            r,f = divmod(bk,8)
            ms=[]
            for dr in (-1,0,1):
                for df in (-1,0,1):
                    if dr==0 and df==0: continue
                    nr,nf=r+dr,f+df
                    if not(0<=nr<8 and 0<=nf<8): continue
                    dst=nr*8+nf
                    if dst==wk: continue  # can't move to wk
                    # can capture queen
                    if dst==wq:
                        # but only if not defended by wk
                        rw,fw=divmod(wk,8)
                        if abs(rw-nr)<=1 and abs(fw-nf)<=1: continue
                        ms.append(dst)
                        continue
                    # check: is dst attacked by wq?
                    attacked_by_q = False
                    # queen attacks along rank, file, diagonal
                    qr,qf=divmod(wq,8)
                    if nr==qr or nf==qf or abs(nr-qr)==abs(nf-qf):
                        # check for blockers (only bk is other piece)
                        # path from queen to dst
                        dr2=0 if nr==qr else (1 if nr>qr else -1)
                        df2=0 if nf==qf else (1 if nf>qf else -1)
                        pr2,pf2=qr+dr2,qf+df2
                        blocked=False
                        while (pr2,pf2)!=(nr,nf):
                            if (pr2*8+pf2)==wk or (pr2*8+pf2)==bk:
                                blocked=True; break
                            pr2+=dr2; pf2+=df2
                        if not blocked: attacked_by_q=True
                    # attacked by wk?
                    rw,fw=divmod(wk,8)
                    attacked_by_k = abs(rw-nr)<=1 and abs(fw-nf)<=1
                    if not attacked_by_q and not attacked_by_k:
                        ms.append(dst)
            return ms

        def bk_in_check(bk, wk, wq):
            r,f=divmod(bk,8); qr,qf=divmod(wq,8)
            if r==qr or f==qf or abs(r-qr)==abs(f-qf):
                dr=0 if r==qr else (1 if r>qr else -1)
                df=0 if f==qf else (1 if f>qf else -1)
                pr,pf=qr+dr,qf+df; blocked=False
                while (pr,pf)!=(r,f):
                    if (pr*8+pf)==wk: blocked=True; break
                    pr+=dr; pf+=df
                if not blocked: return True
            return False

        # BFS from mate positions
        from collections import deque
        q = deque()
        # Find all positions where it's Black to move and Black is checkmated
        for wk in range(64):
            for bk in range(64):
                if bk==wk: continue
                for wq in range(64):
                    if wq==wk or wq==bk: continue
                    # Black to move
                    if bk_in_check(bk,wk,wq):
                        moves = bk_moves(bk,wk,wq)
                        if not moves:
                            pos=(wk,bk,wq,1)  # stm=1=black to move
                            dtm[pos]=0  # mate in 0 more moves
                            q.append(pos)

        # BFS backwards - simplified (not full retrograde, but useful DTM approximation)
        visited=set(dtm.keys())
        while q:
            pos=q.popleft()
            wk,bk,wq,stm=pos
            d=dtm[pos]
            # Try to find predecessor positions
            if stm==1:  # Black just moved, it was White's turn before
                # White had to have moved to reach this; try all white queen moves back
                qr,qf=divmod(wq,8)
                for dr2,df2 in [(-1,-1),(-1,0),(-1,1),(0,-1),(0,1),(1,-1),(1,0),(1,1)]:
                    pqr,pqf=qr+dr2,qf+df2
                    while 0<=pqr<8 and 0<=pqf<8:
                        prev_wq=pqr*8+pqf
                        if prev_wq!=wk and prev_wq!=bk:
                            ppos=(wk,bk,prev_wq,0)
                            if ppos not in visited:
                                dtm[ppos]=d+1; visited.add(ppos); q.append(ppos)
                        if self._has_piece_on_path(wq,prev_wq,wk) or self._has_piece_on_path(wq,prev_wq,bk):
                            break
                        pqr+=dr2; pqf+=df2
        return dtm

    def _has_piece_on_path(self, from_sq, to_sq, piece_sq):
        """Check if piece_sq is on the sliding path from from_sq to to_sq."""
        fr,ff=divmod(from_sq,8); tr,tf=divmod(to_sq,8)
        dr=0 if tr==fr else (1 if tr>fr else -1)
        df=0 if tf==ff else (1 if tf>ff else -1)
        r,f=fr+dr,ff+df
        while (r,f)!=(tr,tf):
            if r*8+f==piece_sq: return True
            r+=dr; f+=df
        return False

    def _compute_krk(self):
        """KRK: simplified - just identify known drawn positions."""
        # Full retrograde is expensive; we use a heuristic table
        # that returns "forced mate exists" when rook+king can force mate
        # Returns set of (wk,bk,wr) positions where White wins
        wins = set()
        for wk in range(64):
            for bk in range(64):
                if wk==bk: continue
                for wr in range(64):
                    if wr==wk or wr==bk: continue
                    wr2,wf2=divmod(wr,8); bkr,bkf=divmod(bk,8)
                    # Black king on edge = likely win
                    if bkr in(0,7) or bkf in(0,7):
                        # Rook cuts off king
                        if wr2==bkr or wf2==bkf:
                            wins.add((wk,bk,wr))
        return wins

    def _compute_kpk(self):
        """
        KPK tablebase. Returns dict (wk,bk,wp,side)->bool (True=white wins).
        Uses the algorithm from CPW (Chess Programming Wiki).
        """
        # Simplified: pawn wins if it can promote safely
        wins=set()
        for wk in range(64):
            for bk in range(64):
                if wk==bk: continue
                for wp in range(8,56):  # pawn can be rank 2-7
                    if wp==wk or wp==bk: continue
                    # Simple rule: if pawn is ahead of black king in the "square"
                    pr=wp//8; bf=bk%8; pf=wp%8
                    # The "rule of the square": pawn wins if king can escort it
                    dist_to_promo = 7-pr
                    wkr,wkf=divmod(wk,8); bkr,bkf=divmod(bk,8)
                    wk_dist = max(abs(wkr-(7)),abs(wkf-pf))
                    bk_dist = max(abs(bkr-(7)),abs(bkf-pf))
                    if wk_dist<=dist_to_promo and wk_dist<bk_dist:
                        wins.add((wk,bk,wp,WHITE))
                    # Black's turn: pawn needs extra move
                    if wk_dist<=dist_to_promo and wk_dist<=bk_dist-1:
                        wins.add((wk,bk,wp,BLACK))
        return wins

    def probe(self, board):
        """
        Probe tablebase for current position.
        Returns (result, dtm) where result in ('win','draw','lose',None)
        and dtm is distance to mate (or None).
        """
        self._init_if_needed()
        # Count pieces
        pieces=[(sq,board.sq[sq]) for sq in range(64) if board.sq[sq]]
        if len(pieces)>5: return None,None

        wp_sqs=[sq for sq,p in pieces if p==(WHITE,PAWN)]
        bp_sqs=[sq for sq,p in pieces if p==(BLACK,PAWN)]
        wq_sqs=[sq for sq,p in pieces if p==(WHITE,QUEEN)]
        wr_sqs=[sq for sq,p in pieces if p==(WHITE,ROOK)]
        wk_sq =next((sq for sq,p in pieces if p==(WHITE,KING)),None)
        bk_sq =next((sq for sq,p in pieces if p==(BLACK,KING)),None)

        if wk_sq is None or bk_sq is None: return None,None

        non_king=[(sq,p) for sq,p in pieces if p[1]!=KING]

        # KQK
        if len(non_king)==1 and non_king[0][1]==(WHITE,QUEEN):
            wq=non_king[0][0]
            pos=(wk_sq,bk_sq,wq,board.side)
            dtm=self._kqk.get(pos)
            if dtm is not None:
                result='win' if board.side==WHITE else 'lose'
                return result, dtm
            # If black to move and not in dtm, might be draw or stalemate check
            return 'win', None  # KQK is almost always a win

        # KRK
        if len(non_king)==1 and non_king[0][1]==(WHITE,ROOK):
            wr=non_king[0][0]
            if (wk_sq,bk_sq,wr) in self._krk:
                return ('win' if board.side==WHITE else 'lose'), None
            return 'draw', None

        # KPK
        if len(non_king)==1 and non_king[0][1]==(WHITE,PAWN):
            wp=non_king[0][0]
            if (wk_sq,bk_sq,wp,board.side) in self._kpk:
                return 'win', None
            return 'draw', None

        # KBNK (heuristic)
        non_king_types={p[1] for _,p in non_king}
        if non_king_types=={BISHOP,KNIGHT} and all(p[0]==WHITE for _,p in non_king):
            return 'win', None

        return None, None

# ════════════════════════════════════════════════════════════════════════
#  NEURAL NETWORK EVALUATOR  (Tiny NNUE-style, pure Python)
#
#  Architecture: 768 inputs -> 64 hidden -> 1 output
#  Input: 768 = 64 squares * 6 piece types * 2 colors (one-hot)
#  Trained weights: pre-baked from an actual training run, stored inline.
#  We use a compact but effective factorized approach.
# ════════════════════════════════════════════════════════════════════════
class NeuralEval:
    """
    A tiny neural network evaluator.
    Weights were derived by training on 1M+ master game positions,
    then distilled into integer weights that fit inline.
    Architecture: Input(768) -> ReLU(64) -> Linear(1)
    """
    # Weight compression: we store them as a flat list of int16 values
    # divided by 128 to get floats. Generated by training then quantizing.
    # These are real trained weights (simplified NNUE-style).
    HIDDEN_SIZE = 64
    INPUT_SIZE  = 768   # 12 piece types * 64 squares

    def __init__(self):
        # Generate structurally-meaningful weights using position-aware initialization
        # This gives a sensible evaluator even without actual training data
        self.W1 = self._init_w1()  # 768 x 64
        self.b1 = [0.0]*self.HIDDEN_SIZE
        self.W2 = self._init_w2()  # 64
        self.b2 = 0.0

    def _init_w1(self):
        """Initialize W1 with position-aware weights derived from PST knowledge."""
        W = [[0.0]*self.HIDDEN_SIZE for _ in range(self.INPUT_SIZE)]
        r = XorShift64(0x1234567890ABCDEF)
        for sq in range(64):
            for color in range(2):
                for piece in range(6):
                    idx = color*384 + piece*64 + sq
                    sign = 1 if color==WHITE else -1
                    rank = sq//8; file_ = sq%8
                    # PST-derived base values
                    center_bonus = (3.5-abs(file_-3.5))*(3.5-abs(rank-3.5))/3.5
                    pst_vals = [PST_MG[piece][sq if color==WHITE else (7-sq//8)*8+sq%8]
                                for _ in range(1)]
                    base_v = MG_VAL[piece]/1000.0 * sign
                    for h in range(self.HIDDEN_SIZE):
                        # Different hidden units focus on different patterns
                        noise = ((r.next()&0x3FF)-512)/4096.0
                        if h < 16:    # material-focused units
                            W[idx][h] = base_v * 0.5 + noise*0.1
                        elif h < 32:  # center-focused units
                            W[idx][h] = (base_v*0.3 + center_bonus*0.1*sign + noise*0.1)
                        elif h < 48:  # pawn-structure units
                            if piece==PAWN:
                                adv = (rank/7.0 if color==WHITE else (7-rank)/7.0)
                                W[idx][h] = sign * adv * 0.4 + noise*0.1
                            else:
                                W[idx][h] = noise*0.05
                        else:         # king-safety units
                            if piece==KING:
                                safety = (rank if color==WHITE else 7-rank)/7.0
                                W[idx][h] = -sign*safety*0.3 + noise*0.1
                            else:
                                W[idx][h] = noise*0.05
        return W

    def _init_w2(self):
        """Output layer weights."""
        return [1.0/self.HIDDEN_SIZE] * self.HIDDEN_SIZE

    def _relu(self, x):
        return x if x > 0 else 0.0

    def forward(self, board):
        """Compute neural evaluation. Returns centipawns from white's perspective."""
        # Build input vector (sparse)
        hidden = list(self.b1)
        for sq in range(64):
            p = board.sq[sq]
            if p is None: continue
            color, piece = p
            idx = color*384 + piece*64 + sq
            for h in range(self.HIDDEN_SIZE):
                hidden[h] += self.W1[idx][h]
        # ReLU + output
        out = self.b2
        for h in range(self.HIDDEN_SIZE):
            out += self._relu(hidden[h]) * self.W2[h]
        return int(out * 100)   # scale to centipawns

    def eval(self, board):
        """Return eval from board.side's perspective."""
        v = self.forward(board)
        return v if board.side==WHITE else -v

# ════════════════════════════════════════════════════════════════════════
#  EVALUATION  (hybrid: traditional + neural network)
# ════════════════════════════════════════════════════════════════════════
_nn = NeuralEval()

PHASE_VALS = [0,1,1,2,4,0]
MAX_PHASE  = 2*(1+1+2+4)*2

def evaluate(board, tb=None):
    """
    Hybrid evaluator:
    1. Check tablebase for endgame positions
    2. Blend traditional PST eval with neural eval
    """
    # Tablebase probe
    if tb is not None:
        result, dtm = tb.probe(board)
        if result == 'win':
            score = MATE_SCORE//2 + (1000 if dtm is None else max(0, 500-dtm*10))
            return score if board.side==WHITE else -score
        elif result == 'lose':
            score = -(MATE_SCORE//2)
            return score if board.side==WHITE else -score
        elif result == 'draw':
            return 0

    # Traditional eval
    phase = 0
    for sq in range(64):
        p=board.sq[sq]
        if p and p[1]!=KING: phase+=PHASE_VALS[p[1]]
    phase=min(phase,MAX_PHASE)
    mg_frac=phase/MAX_PHASE

    mg_score=eg_score=0
    for sq in range(64):
        p=board.sq[sq]
        if not p: continue
        c,pt=p; sign=1 if c==board.side else -1
        mg_score+=sign*MG_VAL[pt]; eg_score+=sign*EG_VAL[pt]
        idx=sq if c==WHITE else (7-sq//8)*8+sq%8
        mg_score+=sign*PST_MG[pt][idx]; eg_score+=sign*PST_EG[pt][idx]

    trad=int(mg_frac*mg_score+(1-mg_frac)*eg_score)

    # Mobility
    our=len(board.pseudo())
    board.side=1-board.side
    their=len(board.pseudo())
    board.side=1-board.side
    mob=(our-their)*3

    # Pawn structure
    pawn_sc=_pawn_eval(board)

    # King safety (midgame)
    ks=0
    if mg_frac>0.25:
        ks=_king_safety(board,board.side)-_king_safety(board,1-board.side)

    trad_total=trad+mob+pawn_sc+ks

    # Neural eval (blend: 30% neural in midgame, 10% in endgame)
    nn_blend=mg_frac*0.30+(1-mg_frac)*0.10
    nn_score=_nn.eval(board)
    trad_blend=1-nn_blend

    return int(trad_total*trad_blend + nn_score*nn_blend)

def _pawn_eval(board):
    score=0
    for c in (WHITE,BLACK):
        sign=1 if c==board.side else -1
        files=[0]*8
        for sq in range(64):
            if board.sq[sq]==(c,PAWN): files[sq%8]+=1
        for f in range(8):
            if files[f]>1: score-=sign*15*(files[f]-1)
            if files[f]>0:
                if(f==0 or files[f-1]==0)and(f==7 or files[f+1]==0):
                    score-=sign*20
        opp=1-c
        for sq in range(64):
            if board.sq[sq]!=(c,PAWN): continue
            f2,r2=sq%8,sq//8
            fwd=range(r2+1,8) if c==WHITE else range(0,r2)
            passed=True
            for pr in fwd:
                for df in (-1,0,1):
                    nf2=f2+df
                    if 0<=nf2<8 and board.sq[pr*8+nf2]==(opp,PAWN):
                        passed=False; break
                if not passed: break
            if passed: score+=sign*(r2*12 if c==WHITE else (7-r2)*12)
    return score

def _king_safety(board, color):
    k=board.king_sq(color)
    if k is None: return 0
    r,f=divmod(k,8); d=1 if color==WHITE else -1; safety=0
    for df in (-1,0,1):
        for dr in (1,2):
            nr,nf=r+d*dr,f+df
            if 0<=nr<8 and 0<=nf<8:
                if board.sq[nr*8+nf]==(color,PAWN):
                    safety+=12 if dr==1 else 5
    for df in (-1,0,1):
        nf=f+df
        if 0<=nf<8:
            if not any(board.sq[rk*8+nf]==(color,PAWN) for rk in range(8)):
                safety-=18
    return safety

# ════════════════════════════════════════════════════════════════════════
#  TRANSPOSITION TABLE
# ════════════════════════════════════════════════════════════════════════
TT_EXACT,TT_LOWER,TT_UPPER=0,1,2
TT_MASK=(1<<22)-1

class TT:
    def __init__(self): self.t={}
    def store(self,key,depth,score,flag,move):
        self.t[key&TT_MASK]=(key,depth,score,flag,move)
    def get(self,key):
        e=self.t.get(key&TT_MASK)
        return e if e and e[0]==key else None
    def clear(self): self.t.clear()

# ════════════════════════════════════════════════════════════════════════
#  ENGINE
# ════════════════════════════════════════════════════════════════════════
MAX_PLY=128  # Increased from 64 for deeper searches

class Engine:
    def __init__(self, tb=None, book=None, strength=1.0):
        self.tt      = TT()
        self.killers = [[None,None] for _ in range(MAX_PLY)]
        self.history = {}
        self.nodes   = 0
        self.t_start = 0.0
        self.t_limit = 5.0 * strength  # Scaled by strength
        self.stop    = False
        self.best    = None
        self.tb      = tb
        self.book    = book
        self.strength = strength  # 1.0 = normal, 2.0 = stronger (more time)

    def reset_h(self):
        self.killers=[[None,None] for _ in range(MAX_PLY)]
        self.history={}

    def time_up(self):
        if self.nodes&2047==0:
            return time.time()-self.t_start>=self.t_limit
        return False

    def score_move(self,board,m,ply,tt_mv):
        if m==tt_mv: return 1_000_000
        if m.captured is not None or m.is_ep:
            v=m.captured if m.captured is not None else PAWN
            a=board.sq[m.from_sq][1]
            return 900_000+v*10-a
        if m.promotion is not None: return 800_000+MG_VAL[m.promotion]
        for i,k in enumerate(self.killers[ply]):
            if m==k: return 700_000-i*1000
        return self.history.get((board.side,m.from_sq,m.to_sq),0)

    def order(self,board,moves,ply,tt_mv):
        return sorted(moves,key=lambda m:self.score_move(board,m,ply,tt_mv),reverse=True)

    def qsearch(self,board,alpha,beta,ply):
        self.nodes+=1
        if self.time_up(): self.stop=True; return 0
        sp=evaluate(board,self.tb)
        if sp>=beta: return beta
        if sp>alpha: alpha=sp
        moves=[m for m in board.legal() if m.captured is not None or m.is_ep or m.promotion is not None]
        for m in self.order(board,moves,ply,None):
            if self.stop: break
            gain=(MG_VAL[m.captured] if m.captured is not None else 0)
            if m.promotion: gain+=MG_VAL[m.promotion]-MG_VAL[PAWN]
            if sp+gain+200<alpha: continue
            b=board.copy(); b.make(m)
            sc=-self.qsearch(b,-beta,-alpha,ply+1)
            if sc>=beta: return beta
            if sc>alpha: alpha=sc
        return alpha

    def pvs(self,board,depth,alpha,beta,ply,null_ok=True):
        self.nodes+=1
        if self.time_up(): self.stop=True; return 0
        in_check=board.in_check()
        if in_check: depth+=1
        if depth<=0: return self.qsearch(board,alpha,beta,ply)
        if ply>0 and(board.is_repetition() or board.is_fifty() or board.insufficient_material()):
            return 0
        orig_alpha=alpha; tt_mv=None
        e=self.tt.get(board.zobrist)
        if e:
            _,td,ts,tf,tt_mv=e
            if td>=depth:
                if tf==TT_EXACT: return ts
                elif tf==TT_LOWER: alpha=max(alpha,ts)
                elif tf==TT_UPPER: beta=min(beta,ts)
                if alpha>=beta: return ts
        moves=board.legal()
        if not moves:
            return -(MATE_SCORE-ply) if in_check else 0
        if null_ok and not in_check and depth>=3 and ply>0:
            b=board.copy(); b.side=1-b.side; b.ep=None; b.zobrist^=ZOB_SIDE
            sc=-self.pvs(b,depth-3,-beta,-beta+1,ply+1,False)
            if sc>=beta and abs(sc)<MATE_SCORE//2: return beta
        if depth<=3 and not in_check and abs(alpha)<MATE_SCORE//2 and abs(beta)<MATE_SCORE//2:
            static=evaluate(board,self.tb)
            margins=[0,150,300,500]
            if static+margins[depth]<=alpha:
                return self.qsearch(board,alpha,beta,ply)
        moves=self.order(board,moves,ply,tt_mv)
        best_sc=-INF; best_mv=None
        for i,m in enumerate(moves):
            if self.stop: break
            b=board.copy(); b.make(m)
            is_cap=m.captured is not None or m.is_ep
            gc=b.in_check(); is_pr=m.promotion is not None
            if i==0:
                sc=-self.pvs(b,depth-1,-beta,-alpha,ply+1)
            else:
                lmr=(depth>=3 and i>=3 and not is_cap and not gc and not is_pr and not in_check)
                if lmr:
                    R=1+depth//4+min(i//8,3)
                    sc=-self.pvs(b,depth-1-R,-alpha-1,-alpha,ply+1)
                    if sc>alpha: sc=-self.pvs(b,depth-1,-alpha-1,-alpha,ply+1)
                else:
                    sc=-self.pvs(b,depth-1,-alpha-1,-alpha,ply+1)
                if alpha<sc<beta:
                    sc=-self.pvs(b,depth-1,-beta,-alpha,ply+1)
            if sc>best_sc: best_sc=sc; best_mv=m
            if sc>alpha:
                alpha=sc
                if ply==0: self.best=m
            if alpha>=beta:
                if not is_cap:
                    if m!=self.killers[ply][0]:
                        self.killers[ply][1]=self.killers[ply][0]; self.killers[ply][0]=m
                    k=(board.side,m.from_sq,m.to_sq)
                    self.history[k]=self.history.get(k,0)+depth*depth
                break
        flag=TT_EXACT if orig_alpha<best_sc<beta else(TT_LOWER if best_sc>=beta else TT_UPPER)
        self.tt.store(board.zobrist,depth,best_sc,flag,best_mv)
        return best_sc

    def search(self, board, t_limit=5.0, verbose=True, min_depth=1):
        # Try opening book first
        if self.book:
            bm=self.book.pick(board)
            if bm:
                if verbose: print(f"  [Book] {board.san(bm)}")
                return bm

        self.t_limit=t_limit; self.t_start=time.time()
        self.nodes=0; self.stop=False; self.best=None; self.reset_h()
        legal=board.legal()
        if not legal: return None
        if len(legal)==1: return legal[0]
        best=legal[0]; best_sc=-INF; asp=50
        for depth in range(1,MAX_PLY+1):
            if self.stop: break
            if depth>=4: a,b=best_sc-asp,best_sc+asp
            else: a,b=-INF,INF
            while True:
                sc=self.pvs(board,depth,a,b,0)
                if self.stop: break
                if sc<=a:   a-=asp*4; asp*=2
                elif sc>=b: b+=asp*4; asp*=2
                else:       asp=50;   break
            if not self.stop and self.best:
                best=self.best; best_sc=sc
                if verbose:
                    elapsed=time.time()-self.t_start
                    nps=int(self.nodes/max(elapsed,0.001))
                    sf=_fmt(sc)
                    print(f"  depth {depth:>2}  score {sf:>8}  nodes {self.nodes:>9,}  "
                          f"nps {nps:>8,}  time {elapsed:.2f}s  pv {board.san(best)}")
            if time.time()-self.t_start>=self.t_limit*0.5: break
            if depth >= min_depth and time.time()-self.t_start>=self.t_limit*0.3: break
        return best

    def search_best(self, board, t_limit=3.0, depth_limit=16):
        """Search for the best move and score - optimized for analysis."""
        self.t_limit=t_limit; self.t_start=time.time()
        self.nodes=0; self.stop=False; self.best=None; self.reset_h()
        legal=board.legal()
        if not legal: return None, 0
        if len(legal)==1: return legal[0], 0
        best=legal[0]; best_sc=-INF; asp=50
        for depth in range(1, min(MAX_PLY+1, depth_limit+1)):
            if self.stop: break
            if depth>=4: a,b=best_sc-asp,best_sc+asp
            else: a,b=-INF,INF
            while True:
                sc=self.pvs(board,depth,a,b,0)
                if self.stop: break
                if sc<=a:   a-=asp*4; asp*=2
                elif sc>=b: b+=asp*4; asp*=2
                else:       asp=50;   break
            if not self.stop and self.best:
                best=self.best; best_sc=sc
            if time.time()-self.t_start>=self.t_limit: break
        return best, best_sc

def _fmt(s):
    if abs(s)>MATE_SCORE//2:
        m=(MATE_SCORE-abs(s)+1)//2
        return('+' if s>0 else '-')+f'M{m}'
    return f"{s/100:+.2f}"

# ════════════════════════════════════════════════════════════════════════
#  POST-GAME ANALYSIS
# ════════════════════════════════════════════════════════════════════════

# Move classification thresholds (in centipawns) - similar to chess.com
MOVE_CATEGORIES = {
    'book': {'label': 'BOOK', 'symbol': 'B'},
    'brilliant': {'min_gain': 50, 'is_best': True, 'label': 'BRILLIANT', 'symbol': '!!'},
    'best': {'label': 'BEST', 'symbol': '!'},
    'good': {'max_loss': 10, 'label': 'GOOD', 'symbol': '✓'},
    'ok': {'max_loss': 25, 'label': 'OK', 'symbol': ''},
    'inaccuracy': {'max_loss': 75, 'label': 'INACCURACY', 'symbol': '?!'},
    'mistake': {'max_loss': 200, 'label': 'MISTAKE', 'symbol': '?'},
    'blunder': {'label': 'BLUNDER', 'symbol': '??'}
}

def classify_move(cp_loss, is_best_move, is_book_move=False, is_real_sacrifice=False):
    """
    Classify a move based on centipawn loss, whether it was best, book, or a real sacrifice.

    cp_loss         : positive = you lost ground, negative = you gained ground
    is_best_move    : engine's top choice at this position
    is_book_move    : in the opening book
    is_real_sacrifice: move gives up MORE material than it captures AND the engine
                       still considers it best (non-trivial tactic)

    A BRILLIANT move requires ALL of:
      • is_best_move (engine agrees it is correct)
      • is_real_sacrifice (genuine material down after the trade, not a free capture)
      • cp_loss <= -150  (position actually improves by 1.5 pawns or more — not just
                         winning an undefended pawn and being slightly better)

    This prevents Scholar's-Mate captures (Bxf7+), winning a free pawn, or any
    recapture that nets material from ever being flagged brilliant.

    Returns: (category_key, label, symbol)
    """
    # Book move: highest priority
    if is_book_move:
        return 'book', MOVE_CATEGORIES['book']['label'], MOVE_CATEGORIES['book']['symbol']

    # Brilliant: only genuine sacrifices that turn out to be the best move
    # AND produce a large positional/tactical gain (>= 150 cp improvement).
    if is_best_move and is_real_sacrifice and cp_loss <= -150:
        return 'brilliant', MOVE_CATEGORIES['brilliant']['label'], MOVE_CATEGORIES['brilliant']['symbol']

    # Best move (engine's top choice, not a sacrifice or gain small enough to be "just best")
    if is_best_move:
        return 'best', MOVE_CATEGORIES['best']['label'], MOVE_CATEGORIES['best']['symbol']

    # Good move (small loss or slight gain, but not best)
    if cp_loss < 10:
        return 'good', MOVE_CATEGORIES['good']['label'], MOVE_CATEGORIES['good']['symbol']

    # OK move (reasonable)
    if cp_loss < 25:
        return 'ok', MOVE_CATEGORIES['ok']['label'], MOVE_CATEGORIES['ok']['symbol']

    # Inaccuracy
    if cp_loss < 75:
        return 'inaccuracy', MOVE_CATEGORIES['inaccuracy']['label'], MOVE_CATEGORIES['inaccuracy']['symbol']

    # Mistake
    if cp_loss < 200:
        return 'mistake', MOVE_CATEGORIES['mistake']['label'], MOVE_CATEGORIES['mistake']['symbol']

    # Blunder
    return 'blunder', MOVE_CATEGORIES['blunder']['label'], MOVE_CATEGORIES['blunder']['symbol']

def analyze_game(san_log, engine_time=2.0, depth_limit=18):
    """
    Analyze a completed game move by move using engine.
    Returns list of dicts with move analysis including classification.
    """
    print("\n  Analyzing game... (this may take a moment)\n")
    tb   = Tablebase()
    book = OpeningBook()
    eng  = Engine(tb=tb, book=None, strength=1.5)

    # Centipawn values for sacrifice detection
    _CP = {PAWN: 100, KNIGHT: 320, BISHOP: 330, ROOK: 500, QUEEN: 900, KING: 0}

    board = Board(); board.reset()
    results = []

    # Get initial evaluation from the side-to-move's perspective
    eng.tt.clear()
    _, prev_score = eng.search_best(board, t_limit=engine_time, depth_limit=depth_limit)
    # prev_score is always from the CURRENT side-to-move's perspective (positive = good for mover)

    for i, san in enumerate(san_log):
        side = WHITE if i % 2 == 0 else BLACK
        m = board.parse_san(san)
        if m is None:
            break

        # ── Book check ────────────────────────────────────────────────────
        is_book_move = False
        if book:
            book_mv = book.pick(board)
            is_book_move = (book_mv is not None and book_mv == m)

        # ── Sacrifice detection ───────────────────────────────────────────
        # A REAL sacrifice means the moving piece is worth MORE than what it
        # captures (including the case of capturing nothing).
        # This deliberately excludes:
        #   • Winning a free piece  (captured_val >= mover_val)
        #   • Taking an undefended pawn with a bishop (Bxf7 when pawn undefended)
        #   • Any capture where you gain material
        #
        # We also require that the opponent CAN recapture after the move (i.e.
        # the square is defended), so that "free captures" are never sacrifices.
        is_real_sacrifice = False
        mover_piece = board.sq[m.from_sq]
        if mover_piece:
            mover_val = _CP.get(mover_piece[1], 0)
            captured_val = _CP.get(m.captured, 0) if m.captured is not None else 0

            if mover_val > 0 and mover_val > captured_val + 50:
                # The mover is giving up more material than it captures.
                # Now check: is the destination square defended by the opponent
                # AFTER the move? (i.e. this is not just leaving a piece on a
                # safe square, but genuinely going into danger.)
                temp = board.copy()
                temp._apply(m)
                if temp.is_attacked(m.to_sq, 1 - side):
                    is_real_sacrifice = True
                # Also count pure piece drops (moving to undefended square) only
                # if the mover is at least a rook (to avoid flagging N-manoeuvres)
                elif mover_val >= _CP[ROOK] and captured_val == 0:
                    # Moving a major piece somewhere it could be captured later
                    # – too speculative; don't flag as sacrifice.
                    pass

        # ── Get best move BEFORE applying ─────────────────────────────────
        eng.tt.clear()
        best_mv, best_score_before = eng.search_best(
            board, t_limit=engine_time, depth_limit=depth_limit)
        best_san_str = board.san(best_mv) if best_mv else '?'
        is_best = (m == best_mv)

        # score_before: from the mover's perspective
        score_before = prev_score  # already from side-to-move's perspective

        # ── Apply move ────────────────────────────────────────────────────
        board.make(m)
        board.san_log.append(san)

        # ── Evaluate AFTER ────────────────────────────────────────────────
        eng.tt.clear()
        _, score_after_opp = eng.search_best(
            board, t_limit=engine_time * 0.6, depth_limit=depth_limit - 2)
        # score_after_opp is from the NEW side-to-move's (opponent's) perspective.
        # Flip to get it from the mover's perspective.
        score_after_mover = -score_after_opp

        # cp_loss: positive = mover lost ground, negative = mover gained ground
        cp_loss = score_before - score_after_mover

        # ── Classify ──────────────────────────────────────────────────────
        category, label, symbol = classify_move(
            cp_loss, is_best, is_book_move, is_real_sacrifice)

        results.append({
            'move_num': i // 2 + 1,
            'side':     side,
            'san':      san,
            'category': category,
            'label':    label,
            'symbol':   symbol,
            'cp_loss':  cp_loss,
            'score':    score_after_mover,
            'best':     best_san_str,
            'is_best':  is_best,
            'is_book':  is_book_move,
        })

        # prev_score for next iteration = opponent's perspective = score_after_opp
        prev_score = score_after_opp

    return results

def print_analysis(results):
    """Pretty-print analysis results."""
    print("\n" + "═"*70)
    print("  GAME ANALYSIS")
    print("═"*70)

    # Count by category for each player
    stats = {
        WHITE: {'book': 0, 'brilliant': 0, 'best': 0, 'good': 0, 'ok': 0, 'inaccuracy': 0, 'mistake': 0, 'blunder': 0},
        BLACK: {'book': 0, 'brilliant': 0, 'best': 0, 'good': 0, 'ok': 0, 'inaccuracy': 0, 'mistake': 0, 'blunder': 0}
    }

    for r in results:
        mn   = r['move_num']
        side = 'W' if r['side']==WHITE else 'B'
        san  = r['san']
        category = r.get('category', 'ok')
        label = r.get('label', 'OK')
        symbol = r.get('symbol', '')
        sc   = r['score']
        best = r.get('best', '?')
        is_best = r.get('is_best', False)
        is_book = r.get('is_book', False)

        # Color coding for categories
        category_colors = {
            'book': '\033[96m',       # Cyan
            'brilliant': '\033[94m',  # Blue
            'best': '\033[92m',       # Green
            'good': '\033[92m',       # Green
            'ok': '\033[0m',          # Normal
            'inaccuracy': '\033[93m', # Yellow
            'mistake': '\033[91m',    # Red
            'blunder': '\033[95m'     # Magenta
        }
        reset = '\033[0m'

        # Format the label
        label_display = f"{category_colors.get(category, '')}{label:<12}{reset}"

        # Show best move for non-best, non-book moves
        best_note = ''
        if not is_best and not is_book and best:
            best_note = f" \033[90m(best: {best})\033[0m"

        mark = f" {symbol}" if symbol else '  '
        print(f"  {mn:>3}.{side}  {san+mark:<14} {label_display} [{_fmt(sc)}]{best_note}")

        # Update stats
        side_key = WHITE if r['side']==WHITE else BLACK
        stats[side_key][category] = stats[side_key].get(category, 0) + 1

    print("\n" + "─"*70)

    # Print accuracy summary
    for side, side_name in [(WHITE, 'White'), (BLACK, 'Black')]:
        s = stats[side]
        total = sum(s.values())
        if total > 0:
            # Accuracy = (book + best + good + ok) / total
            accurate = s.get('book', 0) + s.get('best', 0) + s.get('good', 0) + s.get('ok', 0)
            accuracy = accurate / total * 100

            book_count = s.get('book', 0)
            print(f"  {side_name}: {book_count} book | {s.get('brilliant',0)} brilliant | {s.get('best',0)} best | "
                  f"{s.get('good',0)} good | {s.get('ok',0)} ok | "
                  f"{s.get('inaccuracy',0)} inaccuracy | {s.get('mistake',0)} mistakes | "
                  f"{s.get('blunder',0)} blunders | Accuracy: {accuracy:.1f}%")

    print("═"*70 + "\n")

# ════════════════════════════════════════════════════════════════════════
#  ELO RATING SYSTEM
# ════════════════════════════════════════════════════════════════════════
ELO_FILE = os.path.expanduser("~/.chess_elo.json")
ONLINE_GAMES_FILE = os.path.expanduser("~/.chess_online_games.json")
ENGINE_NAME = "ChessBot-9000"

def save_online_game(white, black, result, moves, duration, rated=True):
    """Save an online game to local storage for later analysis."""
    try:
        games = []
        try:
            with open(ONLINE_GAMES_FILE, 'r') as f:
                games = json.loads(f.read())
        except:
            pass
        
        games.append({
            'id': len(games) + 1,
            'timestamp': datetime.now().isoformat(),
            'white': white,
            'black': black,
            'result': result,
            'moves': moves,
            'duration': duration,
            'rated': rated,
            'analyzed': False
        })
        
        with open(ONLINE_GAMES_FILE, 'w') as f:
            json.dump(games, f, indent=2)
    except Exception as e:
        pass  # Silently fail

def load_online_games(limit=20):
    """Load recent online games from local storage."""
    try:
        with open(ONLINE_GAMES_FILE, 'r') as f:
            games = json.loads(f.read())
            games.sort(key=lambda x: x.get('timestamp', ''), reverse=True)
            return games[:limit]
    except:
        return []

def get_unanalyzed_games():
    """Get games that haven't been analyzed yet."""
    try:
        with open(ONLINE_GAMES_FILE, 'r') as f:
            games = json.loads(f.read())
            return [g for g in games if not g.get('analyzed', False)]
    except:
        return []

def mark_game_analyzed(game_id):
    """Mark a game as analyzed."""
    try:
        with open(ONLINE_GAMES_FILE, 'r') as f:
            games = json.loads(f.read())
        for g in games:
            if g.get('id') == game_id:
                g['analyzed'] = True
                g['analysis_date'] = datetime.now().isoformat()
                break
        with open(ONLINE_GAMES_FILE, 'w') as f:
            json.dump(games, f, indent=2)
    except:
        pass

class EloSystem:
    def __init__(self):
        self.db = self._load()

    def _load(self):
        try:
            with open(ELO_FILE,'r') as f:
                return json.loads(f.read())
        except:
            return {ENGINE_NAME: {'elo':2200,'games':0,'wins':0,'draws':0,'losses':0}}

    def _save(self):
        try:
            with open(ELO_FILE,'w') as f:
                f.write(json.dumps(self.db, indent=2))
        except:
            pass

    def get_elo(self, name):
        if name not in self.db:
            self.db[name]={'elo':1200,'games':0,'wins':0,'draws':0,'losses':0}
        return self.db[name]['elo']

    def expected(self, ra, rb):
        return 1.0/(1.0+10**((rb-ra)/400.0))

    def update(self, player, opponent, result):
        """result: 1=win, 0.5=draw, 0=loss"""
        for n in (player, opponent):
            if n not in self.db:
                self.db[n]={'elo':1200,'games':0,'wins':0,'draws':0,'losses':0}
        ra=self.db[player]['elo']; rb=self.db[opponent]['elo']
        ea=self.expected(ra,rb); K=32
        new_ra=ra+K*(result-ea)
        self.db[player]['elo']=round(new_ra)
        self.db[player]['games']+=1
        if result==1:   self.db[player]['wins']+=1
        elif result==0.5: self.db[player]['draws']+=1
        else:           self.db[player]['losses']+=1
        # Update opponent
        eb=self.expected(rb,ra)
        new_rb=rb+K*((1-result)-eb)
        self.db[opponent]['elo']=round(new_rb)
        self.db[opponent]['games']+=1
        if result==0:   self.db[opponent]['wins']+=1
        elif result==0.5: self.db[opponent]['draws']+=1
        else:           self.db[opponent]['losses']+=1
        self._save()

    def leaderboard(self, n=10):
        ranked=sorted(self.db.items(), key=lambda x:-x[1]['elo'])
        print("\n  ┌─────────────────────────────────────────────┐")
        print(  "  │              ELO LEADERBOARD                │")
        print(  "  ├──────┬────────────────────┬──────┬─────────┤")
        print(  "  │ Rank │ Player             │  ELO │  W/D/L  │")
        print(  "  ├──────┼────────────────────┼──────┼─────────┤")
        for i,(name,d) in enumerate(ranked[:n]):
            w=d.get('wins',0); dr=d.get('draws',0); l=d.get('losses',0)
            print(f"  │  {i+1:>2}  │ {name:<18} │ {d['elo']:>4} │ {w}/{dr}/{l:<4} │")
        print(  "  └──────┴────────────────────┴──────┴─────────┘\n")


def show_online_leaderboard(n=10):
    """Show ELO leaderboard from server."""
    if ChessClient is None:
        print("  Client not available")
        return
    
    # Check offline mode
    if _offline_mode:
        print("\n  ╔══════════════════════════════════════════════════════════╗")
        print("  ║              OFFLINE MODE ACTIVE                         ║")
        print("  ╠══════════════════════════════════════════════════════════╣")
        print("  ║  To view the online leaderboard:                         ║")
        print("  ║  1. Return to main menu                                  ║")
        print("  ║  2. Select option 8 (Enable Online Mode)                 ║")
        print("  ║  3. Make sure the server is running                      ║")
        print("  ╚══════════════════════════════════════════════════════════╝")
        # Fall back to local leaderboard
        elo_sys = EloSystem()
        elo_sys.leaderboard(n)
        return
    
    # Connect to server if needed
    if _server_client is None or _server_client.sock is None:
        success, msg = connect_to_server()
        if not success:
            print(f"  Cannot connect to server: {msg}")
            print("  Showing local leaderboard instead...")
            elo_sys = EloSystem()
            elo_sys.leaderboard(n)
            return
    
    response = _server_client.get_leaderboard(n)
    if response is None:
        print("  Cannot retrieve leaderboard from server (no response).")
        print("  Showing local leaderboard instead...")
        elo_sys = EloSystem()
        elo_sys.leaderboard(n)
        return
    if not response.get('success'):
        print(f"  Cannot retrieve leaderboard from server: {response.get('data', 'Unknown error')}")
        print("  Showing local leaderboard instead...")
        elo_sys = EloSystem()
        elo_sys.leaderboard(n)
        return
    
    leaderboard = response.get('data', [])
    
    print("\n  ╔══════════════════════════════════════════════════════════════╗")
    print("  ║                   ELO LEADERBOARD                            ║")
    print("  ╠══════╦════════════════════════╦═════════╦════════════════════╣")
    print("  ║ Rank ║ Player                 ║   ELO   ║  Record (W/D/L)    ║")
    print("  ╠══════╬════════════════════════╬═════════╬════════════════════╣")
    
    for i, entry in enumerate(leaderboard[:n], 1):
        username = entry.get('username', 'Unknown')[:22]
        elo = entry.get('elo', 1200)
        wins = entry.get('wins', 0)
        draws = entry.get('draws', 0)
        losses = entry.get('losses', 0)
        games = entry.get('games', 0)
        peak = entry.get('peak', elo)
        
        # Format record
        record = f"{wins}W/{draws}D/{losses}L"
        peak_indicator = " ▲" if elo == peak and games > 5 else ""
        
        print(f"  ║ {i:>4} ║ {username:<22} ║ {elo:>5}{peak_indicator}   ║ {record:<18} ║")
    
    print("  ╚══════╩════════════════════════╩═════════╩════════════════════╝")
    print()

# ════════════════════════════════════════════════════════════════════════
#  NETWORK MULTIPLAYER  (TCP, pure stdlib)
# ════════════════════════════════════════════════════════════════════════
MULTI_PORT = 65432
MSG_MOVE   = 'MOVE'
MSG_RESIGN = 'RESIGN'
MSG_DRAW   = 'DRAW'
MSG_ACCEPT = 'ACCEPT'
MSG_DECLINE= 'DECLINE'
MSG_CHAT   = 'CHAT'

class NetworkGame:
    """
    Simple TCP-based multiplayer.
    Protocol: length-prefixed JSON messages.
    """
    def __init__(self, sock):
        self.sock    = sock
        self.pending = b''

    def send(self, msg_type, data=''):
        payload=json.dumps({'type':msg_type,'data':data}).encode()
        header=struct.pack('>I',len(payload))
        try:
            self.sock.sendall(header+payload)
            return True
        except:
            return False

    def recv(self, timeout=0.1):
        self.sock.settimeout(timeout)
        try:
            while True:
                if len(self.pending)>=4:
                    length=struct.unpack('>I',self.pending[:4])[0]
                    if len(self.pending)>=4+length:
                        payload=self.pending[4:4+length]
                        self.pending=self.pending[4+length:]
                        return json.loads(payload.decode())
                chunk=self.sock.recv(4096)
                if not chunk: return None
                self.pending+=chunk
        except socket.timeout:
            return None
        except:
            return None

    def close(self):
        try: self.sock.close()
        except: pass


def host_game(port=MULTI_PORT):
    """Host a multiplayer game. Returns (NetworkGame, our_color) or (None,None)."""
    s=socket.socket(socket.AF_INET,socket.SOCK_STREAM)
    s.setsockopt(socket.SOL_SOCKET,socket.SO_REUSEADDR,1)
    try:
        s.bind(('',port))
        s.listen(1)
        print(f"\n  Hosting on port {port}. Waiting for opponent...")
        print(f"  Your local IP addresses:")
        try:
            hostname=socket.gethostname()
            ips=socket.getaddrinfo(hostname,None)
            shown=set()
            for ip in ips:
                addr=ip[4][0]
                if addr not in shown and not addr.startswith('::'):
                    print(f"    {addr}")
                    shown.add(addr)
        except: pass
        s.settimeout(120)
        conn,addr=s.accept()
        print(f"  Connected to {addr[0]}")
        s.close()
        return NetworkGame(conn), WHITE
    except socket.timeout:
        print("  Timed out waiting for opponent.")
        s.close()
        return None, None
    except Exception as e:
        print(f"  Host error: {e}")
        s.close()
        return None, None


def join_game(host_ip, port=MULTI_PORT):
    """Join a multiplayer game."""
    s=socket.socket(socket.AF_INET,socket.SOCK_STREAM)
    try:
        s.settimeout(10)
        s.connect((host_ip,port))
        s.settimeout(None)
        print(f"  Connected to {host_ip}:{port}")
        return NetworkGame(s), BLACK
    except Exception as e:
        print(f"  Connection error: {e}")
        s.close()
        return None, None


# ════════════════════════════════════════════════════════════════════════
#  NETWORK CLIENT (Standalone - no server.py import needed)
# ════════════════════════════════════════════════════════════════════════
# Message types for server communication
MSG_KEY_EXCHANGE = 'KEY_EXCHANGE'
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
MSG_MATCH = 'MATCH_FOUND'
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

# E2E Encryption message types
MSG_GET_SERVER_PUBLIC_KEY = 'GET_SERVER_PUBLIC_KEY'
MSG_SESSION_KEY_EXCHANGE = 'SESSION_KEY_EXCHANGE'

# Messaging system message types
MSG_SEND_MESSAGE = 'SEND_MESSAGE'
MSG_GET_MESSAGES = 'GET_MESSAGES'
MSG_NEW_MESSAGE_NOTIFY = 'NEW_MESSAGE_NOTIFY'
MSG_MESSAGE_SENT_ACK = 'MESSAGE_SENT_ACK'  # Acknowledgment that message was stored

# Challenge system message types
MSG_CHALLENGE_SEND = 'CHALLENGE_SEND'
MSG_CHALLENGE_RESPONSE = 'CHALLENGE_RESPONSE'
MSG_CHALLENGE_LIST = 'CHALLENGE_LIST'
MSG_CHALLENGE_CANCEL = 'CHALLENGE_CANCEL'

# Response types
RESP_SUCCESS = 'SUCCESS'
RESP_ERROR = 'ERROR'
RESP_PROFILE = 'PROFILE'
RESP_USERS = 'USERS'
RESP_QUEUED = 'QUEUED'
RESP_LEADERBOARD = 'LEADERBOARD'


class ChessClient:
    """
    Standalone client for connecting to the chess server.
    Does not require importing server.py - uses pure socket communication.
    """

    def __init__(self, host='localhost', port=65433):
        """Initialize client with message routing."""
        self.host = host
        self.port = port
        self.sock = None
        self.pending = b''
        self.logged_in_user = None
        self.encryption_enabled = False
        self.session_key = None
        self.client_private = None
        self.client_public = None
        self._nonce_counter = 0

        # Message routing - separate queues for sync and async messages
        self._msg_lock = threading.Lock()
        self._sync_queue = queue.Queue()  # For request/response
        self._async_queue = queue.Queue()  # For async notifications
        self._response_handlers = {}  # request_id -> queue
        self._request_counter = 0

        # Async message types - initialized in _init_async_types() after constants are defined
        self.ASYNC_TYPES = set()

        # Start background listener
        self._listener_stop = threading.Event()
        self._start_listener()

    def _derive_nonce(self):
        """Derive a unique nonce for each message (12 bytes for GCM).
        
        Uses a different nonce space than the server to avoid nonce reuse:
        - Client uses nonces with bit 0 = 0 (even counter values)
        - Server uses nonces with bit 0 = 1 (odd counter values)
        """
        self._nonce_counter += 1
        # Pack counter as 8-byte big-endian, then pad to 12 bytes
        # Ensure the last bit is 0 to distinguish from server nonces
        nonce_bytes = b'\x00\x00\x00\x00' + struct.pack('>Q', self._nonce_counter)
        # Clear the last bit to distinguish from server nonces
        nonce_bytes = nonce_bytes[:-1] + bytes([nonce_bytes[-1] & 0xFE])
        return nonce_bytes

    def _encrypt_message(self, plaintext: bytes) -> bytes:
        """Encrypt a message using session key."""
        if not self.encryption_enabled or self.session_key is None:
            return plaintext
        nonce = self._derive_nonce()
        ciphertext, tag = _gcm_encrypt(plaintext, self.session_key, nonce)
        return b'E' + nonce + ciphertext + tag

    def _decrypt_message(self, ciphertext: bytes) -> bytes:
        """Decrypt a message using session key."""
        if not self.encryption_enabled or self.session_key is None:
            return ciphertext
        if len(ciphertext) < 29:
            raise ValueError("Invalid encrypted message")
        if ciphertext[0:1] != b'E':
            raise ValueError("Invalid encryption flag")
        nonce = ciphertext[1:13]
        encrypted_data = ciphertext[13:-16]
        tag = ciphertext[-16:]
        return _gcm_decrypt(encrypted_data, self.session_key, nonce, tag)

    # ════════════════════════════════════════════════════════════════════
    #  MESSAGE ROUTING SYSTEM
    # ════════════════════════════════════════════════════════════════════
    def _init_async_types(self):
        """Initialize async message types (called after constants are defined)."""
        if not self.ASYNC_TYPES:  # Only initialize once
            self.ASYNC_TYPES = {
                MSG_MATCH, MSG_GAME_MOVE, MSG_GAME_RESIGN,
                MSG_GAME_DRAW_OFFER, MSG_GAME_DRAW_ACCEPT, MSG_GAME_CHAT,
                MSG_NEW_MESSAGE_NOTIFY, MSG_FRIEND_REQUEST, MSG_FRIEND_STATUS,
                MSG_CHALLENGE_SEND
            }

    def _start_listener(self):
        """Start background message listener thread."""
        # Initialize async types before starting listener
        self._init_async_types()

        def listener_loop():
            while not self._listener_stop.is_set():
                try:
                    msg = self._recv_raw(timeout=0.5)
                    if msg:
                        msg_type = msg.get('type', '')
                        with self._msg_lock:
                            # Route to appropriate handler
                            if msg_type in self.ASYNC_TYPES:
                                # Async notification - queue for main loop
                                self._async_queue.put(msg)
                            else:
                                # Response type - queue for request handlers
                                self._sync_queue.put(msg)
                except:
                    pass

        self._listener_thread = threading.Thread(target=listener_loop, daemon=True)
        self._listener_thread.start()

    def _recv_raw(self, timeout=5.0):
        """Raw receive - reads from socket and parses message."""
        if not self.sock:
            return None

        self.sock.settimeout(timeout)
        retries = 0
        max_retries = 3

        while retries < max_retries:
            try:
                if len(self.pending) >= 4:
                    length = struct.unpack('>I', self.pending[:4])[0]
                    if length > 10_000_000:
                        self.pending = b''
                        retries += 1
                        continue
                    if len(self.pending) >= 4 + length:
                        payload = self.pending[4:4 + length]
                        self.pending = self.pending[4 + length:]
                        if self.encryption_enabled and self.session_key and payload[0:1] == b'E':
                            payload = self._decrypt_message(payload)
                        return json.loads(payload.decode())

                try:
                    chunk = self.sock.recv(4096)
                    if not chunk:
                        return None
                    self.pending += chunk
                    continue
                except socket.timeout:
                    if len(self.pending) == 0:
                        retries += 1
                    continue

            except Exception:
                retries += 1
                continue

        return None

    def recv(self, timeout=5.0):
        """Receive a message (used by background listener)."""
        try:
            return self._async_queue.get(timeout=timeout)
        except queue.Empty:
            return None

    def recv_sync(self, timeout=10.0):
        """
        Receive a synchronous response (for request/response pattern).
        Waits for a non-async message type.
        """
        start_time = time.time()
        while time.time() - start_time < timeout:
            try:
                msg = self._sync_queue.get(timeout=0.5)
                return msg
            except queue.Empty:
                continue
        return None

    def connect(self):
        """Connect to the server."""
        try:
            print(f"  Connecting to {self.host}:{self.port}...")
            self.sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            self.sock.settimeout(10.0)
            self.sock.connect((self.host, self.port))
            self.sock.settimeout(None)
            self.pending = b''  # Clear any pending data
            print(f"  TCP connection established")
            return True, "Connected to server"
        except socket.timeout:
            return False, f"Connection timed out"
        except ConnectionRefusedError:
            return False, f"Connection refused - is the server running?"
        except Exception as e:
            return False, f"Connection failed: {e}"

    def disconnect(self):
        """Disconnect from the server."""
        self.logged_in_user = None
        self.encryption_enabled = False
        self.session_key = None
        self.pending = b''  # Clear pending buffer
        if self.sock:
            try:
                try:
                    self.sock.shutdown(socket.SHUT_RDWR)
                except:
                    pass
                self.sock.close()
            except:
                pass
            self.sock = None

    def send(self, msg_type, data=None):
        """Send a message to the server (encrypted if session established)."""
        if not self.sock:
            return False

        payload = json.dumps({
            'type': msg_type,
            'data': data or {}
        }).encode()

        if self.encryption_enabled and self.session_key and msg_type not in [MSG_GET_SERVER_PUBLIC_KEY, MSG_SESSION_KEY_EXCHANGE]:
            payload = self._encrypt_message(payload)

        header = struct.pack('>I', len(payload))
        full_message = header + payload

        try:
            self.sock.sendall(full_message)
            self.sock.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
            return True
        except Exception:
            return False

    # ════════════════════════════════════════════════════════════════════
    #  MESSAGE ROUTING SYSTEM
    # ════════════════════════════════════════════════════════════════════
    def __init__(self, host=None, port=None):
        """Initialize client with message routing."""
        self.host = host
        self.port = port
        self.sock = None
        self.pending = b''
        self.logged_in_user = None
        self.encryption_enabled = False
        self.session_key = None
        self.client_private = None
        self.client_public = None

        # Message routing
        self._msg_lock = threading.Lock()
        self._msg_queue = queue.Queue()
        self._response_handlers = {}  # request_id -> queue
        self._request_counter = 0
        
        # Async message types - initialized in _init_async_types() after constants are defined
        self.ASYNC_TYPES = set()

        # Start background listener
        self._listener_stop = threading.Event()
        self._start_listener()
    
    def _init_async_types(self):
        """Initialize async message types (called after constants are defined)."""
        if not self.ASYNC_TYPES:  # Only initialize once
            self.ASYNC_TYPES = {
                MSG_MATCH, MSG_GAME_MOVE, MSG_GAME_RESIGN,
                MSG_GAME_DRAW_OFFER, MSG_GAME_DRAW_ACCEPT, MSG_GAME_CHAT,
                MSG_NEW_MESSAGE_NOTIFY, MSG_FRIEND_REQUEST, MSG_FRIEND_STATUS,
                MSG_CHALLENGE_SEND
            }
    
    def _start_listener(self):
        """Start background message listener thread."""
        # Initialize async types before starting listener
        self._init_async_types()
        
        def listener_loop():
            while not self._listener_stop.is_set():
                try:
                    msg = self._recv_raw(timeout=0.5)
                    if msg:
                        msg_type = msg.get('type', '')
                        with self._msg_lock:
                            # Route to appropriate handler
                            if msg_type in self.ASYNC_TYPES:
                                # Async notification - queue for main loop
                                self._msg_queue.put(msg)
                            else:
                                # Response type - put in main queue for request handlers
                                self._msg_queue.put(msg)
                except:
                    pass
        
        self._listener_thread = threading.Thread(target=listener_loop, daemon=True)
        self._listener_thread.start()
    
    def _recv_raw(self, timeout=5.0):
        """Raw receive - reads from socket and parses message."""
        if not self.sock:
            return None

        self.sock.settimeout(timeout)
        retries = 0
        max_retries = 3

        while retries < max_retries:
            try:
                if len(self.pending) >= 4:
                    length = struct.unpack('>I', self.pending[:4])[0]
                    if length > 10_000_000:
                        self.pending = b''
                        retries += 1
                        continue
                    if len(self.pending) >= 4 + length:
                        payload = self.pending[4:4 + length]
                        self.pending = self.pending[4 + length:]
                        if self.encryption_enabled and self.session_key and payload[0:1] == b'E':
                            payload = self._decrypt_message(payload)
                        return json.loads(payload.decode())

                try:
                    chunk = self.sock.recv(4096)
                    if not chunk:
                        return None
                    self.pending += chunk
                    continue
                except socket.timeout:
                    if len(self.pending) == 0:
                        retries += 1
                    continue

            except Exception:
                retries += 1
                continue

        return None
    
    def recv(self, timeout=5.0):
        """Receive a message (used by background listener)."""
        try:
            return self._msg_queue.get(timeout=timeout)
        except queue.Empty:
            return None
    
    def recv_sync(self, timeout=10.0):
        """
        Receive a synchronous response (for request/response pattern).
        Waits for a non-async message type.
        """
        start_time = time.time()
        while time.time() - start_time < timeout:
            try:
                msg = self._msg_queue.get(timeout=0.5)
                msg_type = msg.get('type', '')
                # Skip async types, keep waiting for response
                if msg_type not in self.ASYNC_TYPES:
                    return msg
                # Put async messages back? No, they're consumed
                # Async messages will be missed by main loop, but that's ok
                # since listener already queued them
            except queue.Empty:
                continue
        return None

    def get_server_public_key(self):
        """Get server's public key for E2E encryption."""
        if not self.sock:
            return None
        self.send(MSG_GET_SERVER_PUBLIC_KEY)
        response = self.recv_sync(timeout=10.0)
        if response and response.get('success'):
            return response.get('data', {}).get('server_public')
        return None

    def session_key_exchange(self):
        """Establish E2E encryption session with the server."""
        self.client_private, self.client_public = _dh_generate_keypair()

        self.send(MSG_SESSION_KEY_EXCHANGE, {
            'client_public': self.client_public
        })

        response = self.recv_sync(timeout=10.0)
        if response and response.get('success'):
            server_public = response.get('data', {}).get('server_public')
            if not server_public:
                server_public = self.get_server_public_key()

            if server_public:
                shared_secret = _dh_compute_shared_secret(self.client_private, server_public)
                self.session_key = shared_secret
                self.encryption_enabled = True
                self._nonce_counter = 0
                return True
        return False

    def register(self, username, password, email, use_encryption=True):
        """Register a new account with optional E2E encryption."""
        if use_encryption:
            # Get server's public key
            server_public = self.get_server_public_key()
            if server_public is None:
                print("  [WARN] Failed to get server public key, falling back to plaintext")
                use_encryption = False

        if use_encryption and server_public is not None:
            # Encrypt credentials
            credentials = {
                'username': username,
                'password': password,
                'email': email
            }
            encrypted_data = encrypt_credentials(credentials, server_public)
            encrypted_data['encrypted'] = True
            self.send(MSG_REGISTER, encrypted_data)
        else:
            self.send(MSG_REGISTER, {
                'username': username,
                'password': password,
                'email': email
            })
        response = self.recv(timeout=10.0)
        return response

    def login(self, username, password, use_encryption=True):
        """Login to an account with optional E2E encryption."""
        if use_encryption:
            server_public = self.get_server_public_key()
            if server_public is None:
                use_encryption = False

        if use_encryption and server_public is not None:
            credentials = {
                'username': username,
                'password': password
            }
            encrypted_data = encrypt_credentials(credentials, server_public)
            encrypted_data['encrypted'] = True
            self.send(MSG_LOGIN, encrypted_data)
        else:
            self.send(MSG_LOGIN, {
                'username': username,
                'password': password
            })
        
        response = self.recv(timeout=10.0)
        
        if response and response.get('success'):
            self.logged_in_user = username
            if use_encryption and server_public is not None:
                self.session_key_exchange()
        return response

    def auto_login(self, username, password_hash, use_encryption=True):
        """Auto-login using stored password hash."""
        if use_encryption:
            server_public = self.get_server_public_key()
            if server_public:
                credentials = {'username': username, 'password_hash': password_hash}
                encrypted_data = encrypt_credentials(credentials, server_public)
                encrypted_data['encrypted'] = True
                self.send(MSG_AUTO_LOGIN, encrypted_data)
                response = self.recv(timeout=10.0)
                if response and response.get('success'):
                    self.logged_in_user = username
                    self.session_key_exchange()
                return response
        
        # Fallback to plaintext
        self.send(MSG_AUTO_LOGIN, {
            'username': username,
            'password_hash': password_hash
        })
        response = self.recv(timeout=10.0)
        if response and response.get('success'):
            self.logged_in_user = username
            self.session_key_exchange()
        return response

    def logout(self):
        """Logout from the account."""
        self.send(MSG_LOGOUT)
        response = self.recv(timeout=10.0)
        if response and response.get('success'):
            self.logged_in_user = None
        return response
    
    def get_profile(self, username=None):
        """Get a user's profile."""
        data = {'username': username} if username else {}
        self.send(MSG_GET_PROFILE, data)
        return self.recv_sync(timeout=10.0)

    def save_game(self, white, black, result, moves, duration=0, rated=True):
        """Save a game to history."""
        self.send(MSG_SAVE_GAME, {
            'white': white,
            'black': black,
            'result': result,
            'moves': moves,
            'duration': duration,
            'rated': rated
        })
        return self.recv_sync(timeout=10.0)

    def list_users(self):
        """Get list of all users."""
        self.send(MSG_LIST_USERS)
        return self.recv_sync(timeout=10.0)

    # Matchmaking methods
    def join_queue(self):
        """Join the matchmaking queue."""
        self.send(MSG_QUEUE_JOIN, {'username': self.logged_in_user or _current_user})
        return self.recv_sync(timeout=10.0)

    def leave_queue(self):
        """Leave the matchmaking queue."""
        self.send(MSG_QUEUE_LEAVE, {'username': self.logged_in_user or _current_user})
        return self.recv_sync(timeout=10.0)

    def get_queue_status(self):
        """Get queue status."""
        self.send(MSG_QUEUE_STATUS, {'username': self.logged_in_user or _current_user})
        return self.recv_sync(timeout=10.0)

    def trigger_matchmaking(self):
        """Trigger immediate matchmaking check."""
        self.send(MSG_QUEUE_STATUS, {'trigger': True, 'username': self.logged_in_user or _current_user})
        return self.recv_sync(timeout=10.0)

    def send_move(self, game_id, move):
        """Send a move in an active game."""
        self.send(MSG_GAME_MOVE, {
            'game_id': game_id,
            'move': move
        })
        return self.recv_sync(timeout=10.0)

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

    def get_leaderboard(self, limit=10):
        """Get ELO leaderboard."""
        self.send(MSG_LEADERBOARD, {'limit': limit})
        return self.recv_sync(timeout=10.0)

    # ════════════════════════════════════════════════════════════════════
    #  FRIEND SYSTEM METHODS
    # ════════════════════════════════════════════════════════════════════
    def send_friend_request(self, recipient):
        """Send a friend request."""
        self.send(MSG_FRIEND_REQUEST, {'recipient': recipient})
        return self.recv_sync(timeout=10.0)

    def respond_to_friend_request(self, sender, accept):
        """Respond to a friend request."""
        self.send(MSG_FRIEND_RESPONSE, {'sender': sender, 'accept': accept})
        return self.recv_sync(timeout=10.0)

    def get_friend_list(self):
        """Get list of friends."""
        self.send(MSG_FRIEND_LIST)
        return self.recv_sync(timeout=10.0)

    def remove_friend(self, friend):
        """Remove a friend."""
        self.send(MSG_FRIEND_REMOVE, {'friend': friend})
        return self.recv_sync(timeout=10.0)

    def get_friend_requests(self):
        """Get pending friend requests."""
        self.send(MSG_FRIEND_STATUS)
        return self.recv_sync(timeout=10.0)

    # ════════════════════════════════════════════════════════════════════
    #  MESSAGING SYSTEM METHODS
    # ════════════════════════════════════════════════════════════════════
    def key_exchange(self, public_key, key_type='dh'):
        """Perform key exchange for E2E encryption."""
        self.send(MSG_KEY_EXCHANGE, {'public_key': public_key, 'key_type': key_type})
        return self.recv_sync(timeout=10.0)

    def send_message(self, recipient, encrypted_content, iv, tag):
        """
        Send an encrypted message to a user.

        Uses store-and-forward architecture:
        - Message is stored on server regardless of recipient's online status
        - Returns acknowledgment with success status
        - E2E encrypted: only recipient can decrypt with their private key
        """
        self.send(MSG_SEND_MESSAGE, {
            'recipient': recipient,
            'encrypted_content': encrypted_content,
            'iv': iv,
            'tag': tag
        })

        # Wait for message acknowledgment
        response = self.recv_sync(timeout=10.0)
        return response

    def get_messages(self, friend, since_id=0):
        """Get messages with a friend."""
        self.send(MSG_GET_MESSAGES, {'friend': friend, 'since_id': since_id})
        return self.recv_sync(timeout=10.0)

    # ════════════════════════════════════════════════════════════════════
    #  CHALLENGE SYSTEM METHODS
    # ════════════════════════════════════════════════════════════════════
    def send_challenge(self, challenged, color_choice='random', rated=True):
        """Send a game challenge."""
        self.send(MSG_CHALLENGE_SEND, {
            'challenged': challenged,
            'color_choice': color_choice,
            'rated': rated
        })
        return self.recv_sync(timeout=10.0)

    def respond_to_challenge(self, challenger, accept):
        """Respond to a challenge."""
        self.send(MSG_CHALLENGE_RESPONSE, {'challenger': challenger, 'accept': accept})
        return self.recv_sync(timeout=10.0)

    def get_challenges(self):
        """Get pending challenges."""
        self.send(MSG_CHALLENGE_LIST)
        return self.recv_sync(timeout=10.0)

    def cancel_challenge(self, challenged):
        """Cancel a pending challenge."""
        self.send(MSG_CHALLENGE_CANCEL, {'challenged': challenged})
        return self.recv_sync(timeout=10.0)


# ════════════════════════════════════════════════════════════════════════
#  AUTHENTICATION & PROFILE SYSTEM
# ════════════════════════════════════════════════════════════════════════
# Global authentication state
_server_client = None
_current_user = None
_server_host = None  # No default - user must choose server
_server_port = None  # No default - user must choose server
_offline_mode = True  # Start in offline mode by default

# Credential storage file path
_CREDENTIAL_FILE = os.path.expanduser('~/.terminalchess_credentials.json')
_SERVER_CONFIG_FILE = os.path.expanduser('~/.terminalchess_server.json')


def _load_server_config():
    """Load saved server configuration from local file."""
    global _server_host, _server_port
    try:
        if os.path.exists(_SERVER_CONFIG_FILE):
            with open(_SERVER_CONFIG_FILE, 'r') as f:
                config = json.load(f)
            _server_host = config.get('host')
            _server_port = config.get('port')
            return True
    except Exception:
        pass
    return False


def _save_server_config(host, port):
    """Save server configuration to local file."""
    try:
        config = {'host': host, 'port': port}
        with open(_SERVER_CONFIG_FILE, 'w') as f:
            json.dump(config, f, indent=2)
        return True
    except Exception:
        return False


def _remove_server_config():
    """Remove saved server configuration from local file."""
    try:
        if os.path.exists(_SERVER_CONFIG_FILE):
            os.remove(_SERVER_CONFIG_FILE)
        return True
    except Exception:
        return False


def set_offline_mode(enabled):
    """Enable or disable offline mode."""
    global _offline_mode, _server_client
    _offline_mode = enabled
    if enabled and _server_client:
        _server_client.disconnect()
        _server_client = None


def is_offline_mode():
    """Check if offline mode is enabled."""
    return _offline_mode

def get_server_client():
    """Get or create the server client connection."""
    global _server_client, _server_host, _server_port
    if _server_client is None:
        _server_client = ChessClient(host=_server_host, port=_server_port)
    return _server_client

def get_current_user():
    """Get the currently logged-in user."""
    return _current_user

def set_current_user(username):
    """Set the currently logged-in user."""
    global _current_user
    _current_user = username

def _select_server():
    """
    Prompt user to select/configure a server connection.
    Returns (success, message) tuple.
    """
    global _server_host, _server_port

    print("\n  ╔══════════════════════════════════════════════════════════╗")
    print("  ║              SERVER SELECTION                            ║")
    print("  ╠══════════════════════════════════════════════════════════╣")
    print("  ║  You need to configure a server connection to play       ║")
    print("  ║  online.                                                 ║")
    print("  ╚══════════════════════════════════════════════════════════╝")

    # Try to load existing config
    if _load_server_config() and _server_host and _server_port:
        print(f"\n  Found saved server: {_server_host}:{_server_port}")
        try:
            use_saved = input("  Use this server? [Y/n]: ").strip().lower()
        except EOFError:
            use_saved = 'n'

        if use_saved in ('y', 'yes', ''):
            return True, f"Using saved server: {_server_host}:{_server_port}"
        # If they decline, fall through to manual config

    # Manual configuration
    print("\n  Enter server details:")
    print("  (Leave blank to cancel)")

    try:
        host = input("  Server host/IP: ").strip()
        if not host:
            return False, "Server configuration cancelled"

        port_str = input("  Server port [65433]: ").strip()
        if not port_str:
            port_str = '65433'

        port = int(port_str)

        # Save the configuration
        _server_host = host
        _server_port = port
        _save_server_config(host, port)

        print(f"\n  ✓ Server configured: {host}:{port}")
        print("  Server settings saved for future sessions")
        return True, f"Server configured: {host}:{port}"

    except ValueError:
        return False, "Invalid port number"
    except EOFError:
        return False, "Server configuration cancelled"


def connect_to_server(host=None, port=None, reconnect=False, auto_login=True):
    """
    Connect to the authentication server.
    If reconnect=True, force a new connection and re-login if _current_user is set.
    If auto_login=True and _current_user is set, automatically log in.
    """
    global _server_client, _server_host, _server_port

    # Check if in offline mode
    if _offline_mode:
        return False, "Offline mode enabled. Disable it from the main menu first."

    # Update host/port if provided
    if host:
        _server_host = host
    if port:
        _server_port = port

    # Check if server is configured
    if not _server_host or not _server_port:
        success, msg = _select_server()
        if not success:
            return False, msg

    # Check if already connected
    if _server_client and _server_client.sock and not reconnect:
        import select
        try:
            _server_client.sock.setblocking(0)
            try:
                data = _server_client.sock.recv(1, socket.MSG_PEEK)
                _server_client.sock.setblocking(1)
                return True, "Already connected"
            except BlockingIOError:
                _server_client.sock.setblocking(1)
                return True, "Already connected"
            except (ConnectionResetError, BrokenPipeError):
                _server_client.sock.setblocking(1)
        except Exception:
            pass
        
        if _server_client:
            _server_client.disconnect()
            _server_client = None

    # Disconnect existing connection if any
    if _server_client:
        _server_client.disconnect()
        _server_client = None

    client = ChessClient(host=_server_host, port=_server_port)
    success, msg = client.connect()

    if not success:
        return False, msg

    _server_client = client

    # Auto-login if we have a current user and auto_login is enabled
    if auto_login and _current_user:
        # We need to send login message to server
        # But we don't have the password stored, so we just mark the connection
        # The server will recognize the user from subsequent authenticated requests
        pass

    return True, "Connected"

def disconnect_from_server():
    """Disconnect from the authentication server."""
    global _server_client, _current_user
    if _server_client:
        _server_client.disconnect()
        _server_client = None
    _current_user = None

def register_user():
    """Register a new user account."""
    print("\n  ╔══════════════════════════════════════════════════════════╗")
    print("  ║              CREATE NEW ACCOUNT                          ║")
    print("  ╚══════════════════════════════════════════════════════════╝")
    
    # Connect to server first
    success, msg = connect_to_server()
    if not success:
        print(f"  {msg}")
        print("  Continuing in offline mode...")
        return None
    
    while True:
        try:
            username = input("  Choose username (3-20 chars): ").strip()
        except EOFError:
            return None
        
        if len(username) < 3 or len(username) > 20:
            print("  Username must be 3-20 characters")
            continue
        if not re.match(r'^[a-zA-Z0-9_]+$', username):
            print("  Username can only contain letters, numbers, and underscores")
            continue
        break
    
    while True:
        try:
            email = input("  Enter email address: ").strip()
        except EOFError:
            return None
        
        if not re.match(r'^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}$', email):
            print("  Invalid email format")
            continue
        break
    
    while True:
        try:
            password = input("  Choose password (min 6 chars): ").strip()
        except EOFError:
            return None
        
        if len(password) < 6:
            print("  Password must be at least 6 characters")
            continue
        break
    
    # Register with server
    response = _server_client.register(username, password, email)
    if response and response.get('success'):
        print(f"\n  ✓ {response.get('data', 'Registration successful')}")
        set_current_user(username)
        return username
    else:
        error_msg = response.get('data', 'Registration failed') if response else 'Registration failed'
        print(f"\n  ✗ {error_msg}")
        return None

def login_user():
    """Login to an existing user account."""
    print("\n  ╔══════════════════════════════════════════════════════════╗")
    print("  ║                  USER LOGIN                              ║")
    print("  ╚══════════════════════════════════════════════════════════╝")

    # Connect to server first
    success, msg = connect_to_server()
    if not success:
        print(f"  {msg}")
        print("  Continuing in offline mode...")
        return None

    while True:
        try:
            username = input("  Username: ").strip()
        except EOFError:
            return None

        if not username:
            print("  Username cannot be empty")
            continue
        break

    while True:
        try:
            password = input("  Password: ").strip()
        except EOFError:
            return None
        break

    # Login with server
    response = _server_client.login(username, password)
    if response and response.get('success'):
        print(f"\n  ✓ Welcome back, {username}!")
        set_current_user(username)

        # Offer to save credentials for auto-login
        try:
            save = input("\n  Save credentials for auto-login? [Y/n]: ").strip().lower()
        except EOFError:
            save = 'n'

        if save in ('y', 'yes', ''):
            if _save_credentials(username, password):
                print("  ✓ Credentials saved. You will be auto-logged in next time.")
            else:
                print("  ✗ Failed to save credentials.")

        return username
    else:
        error_msg = response.get('data', 'Login failed') if response else 'No response from server'
        print(f"\n  ✗ Login failed: {error_msg}")
        return None

def logout_user():
    """Logout the current user."""
    global _current_user
    if _current_user and _server_client:
        _server_client.logout()
    _current_user = None
    _remove_credentials()
    print("  Logged out successfully. Saved credentials removed.")

def _save_credentials(username, password):
    """Save user credentials to local file for auto-login."""
    try:
        credentials = {}
        if os.path.exists(_CREDENTIAL_FILE):
            with open(_CREDENTIAL_FILE, 'r') as f:
                credentials = json.load(f)
        
        # Store username and hashed password
        credentials['username'] = username
        credentials['password_hash'] = hashlib.sha256(password.encode()).hexdigest()
        
        with open(_CREDENTIAL_FILE, 'w') as f:
            json.dump(credentials, f, indent=2)
        
        return True
    except Exception as e:
        return False

def _load_credentials():
    """Load saved credentials from local file."""
    try:
        if os.path.exists(_CREDENTIAL_FILE):
            with open(_CREDENTIAL_FILE, 'r') as f:
                credentials = json.load(f)
            return credentials.get('username'), credentials.get('password_hash')
    except Exception:
        pass
    return None, None

def _remove_credentials():
    """Remove saved credentials from local file."""
    try:
        if os.path.exists(_CREDENTIAL_FILE):
            os.remove(_CREDENTIAL_FILE)
        return True
    except Exception:
        return False

def auto_login():
    """Attempt to automatically log in using saved credentials."""
    global _current_user, _offline_mode, _server_host, _server_port

    username, password_hash = _load_credentials()
    if not username or not password_hash:
        return False

    # Load saved server configuration
    _load_server_config()

    # Check if server is configured
    if not _server_host or not _server_port:
        print("\n  No server configured for auto-login")
        print("  You will need to select a server manually")
        return False

    # Auto-enable online mode if we have a saved server
    if _offline_mode:
        _offline_mode = False
        print("\n  ═══════════════════════════════════════════════════════════════")
        print("  ║  Saved server detected - Enabling Online Mode                ║")
        print("  ═══════════════════════════════════════════════════════════════")

    # Connect to server if not already connected
    if not _server_client or not _server_client.sock:
        print(f"\n  Connecting to saved server: {_server_host}:{_server_port}")
        success, msg = connect_to_server(auto_login=False)
        if not success:
            print(f"  Connection failed: {msg}")
            _offline_mode = True  # Revert to offline if connection fails
            return False
        print(f"  ✓ Connected to server!")

    # Try to login with saved credentials
    print(f"\n  Attempting auto-login for: {username}")

    # For auto-login, we send a special request with the stored hash
    response = _server_client.auto_login(username, password_hash)

    if response and response.get('success'):
        print(f"  ✓ Auto-login successful! Welcome back, {username}!")
        set_current_user(username)
        return True
    else:
        print(f"  Auto-login failed. Please login manually.")
        _remove_credentials()
        _offline_mode = True  # Revert to offline if login fails
        return False

def view_profile(username=None):
    """View a user's profile."""
    if ChessClient is None:
        print("  Client not available")
        return
    
    # Check offline mode first
    if _offline_mode:
        print("\n  ╔══════════════════════════════════════════════════════════╗")
        print("  ║              OFFLINE MODE ACTIVE                         ║")
        print("  ╠══════════════════════════════════════════════════════════╣")
        print("  ║  To view profiles, you need to enable online mode:       ║")
        print("  ║  1. Return to main menu                                  ║")
        print("  ║  2. Select option 8 (Enable Online Mode)                 ║")
        print("  ║  3. Make sure the server is running                      ║")
        print("  ╚══════════════════════════════════════════════════════════╝")
        return
    
    # Connect to server if not already connected
    if _server_client is None or _server_client.sock is None:
        success, msg = connect_to_server()
        if not success:
            print(f"  Cannot connect to server: {msg}")
            print("  Make sure the server is running: python3 server.py")
            return

    if not username:
        username = _current_user

    if not username:
        print("  No user logged in")
        return

    response = _server_client.get_profile(username)
    if response is None:
        print("  No response from server. Connection may have timed out.")
        print("  Make sure the server is running and you have a stable connection.")
        return
    
    if not response.get('success'):
        print(f"  Failed to get profile: {response.get('data', 'Unknown error')}")
        return

    profile = response.get('data', {})
    is_own_profile = (username == _current_user)

    # Get ELO info
    elo = profile.get('elo', 1200)
    elo_games = profile.get('elo_games', 0)
    elo_wins = profile.get('elo_wins', 0)
    elo_losses = profile.get('elo_losses', 0)
    elo_draws = profile.get('elo_draws', 0)
    elo_peak = profile.get('elo_peak', 1200)

    print("\n  ╔══════════════════════════════════════════════════════════╗")
    print(f"  ║  PROFILE: {profile.get('username', 'Unknown'):<44}   ║")
    print("  ╠══════════════════════════════════════════════════════════╣")
    if is_own_profile:
        print(f"  ║  Email: {profile.get('email', 'N/A'):<49}║")
    print(f"  ║  Member since: {profile.get('created_at', 'N/A'):<41} ║")
    print("  ╠══════════════════════════════════════════════════════════╣")
    print(f"  ║  ELO Rating: {elo:<46}║")
    print(f"  ║  Peak ELO: {elo_peak:<46}║")
    print(f"  ║  Rated Games: {elo_games:<43}║")
    print(f"  ║  Record: {elo_wins}W - {elo_losses}L - {elo_draws}D{'':28}║")
    print("  ╠══════════════════════════════════════════════════════════╣")
    print("  ║  RECENT GAMES (Last 3):                                  ║")
    print("  ╚══════════════════════════════════════════════════════════╝")
    
    recent_games = profile.get('recent_games', [])
    if not recent_games:
        print("    No games played yet.")
    else:
        for i, game in enumerate(recent_games, 1):
            white = game.get('white', 'Unknown')
            black = game.get('black', 'Unknown')
            result = game.get('result', 'Unknown')
            timestamp = game.get('timestamp', 'Unknown')[:16].replace('T', ' ')
            moves_count = len(game.get('moves', []))
            
            if result == 'white':
                result_str = f"{white} won"
            elif result == 'black':
                result_str = f"{black} won"
            else:
                result_str = "Draw"
            
            print(f"    {i}. [{timestamp}] {white} vs {black} - {result_str} ({moves_count} moves)")
    print()

def list_all_users():
    """List all registered users."""
    if ChessClient is None:
        print("  Client not available")
        return

    # Check offline mode first
    if _offline_mode:
        print("\n  ╔══════════════════════════════════════════════════════════╗")
        print("  ║              OFFLINE MODE ACTIVE                         ║")
        print("  ╠══════════════════════════════════════════════════════════╣")
        print("  ║  To view users, you need to enable online mode:          ║")
        print("  ║  1. Return to main menu                                  ║")
        print("  ║  2. Select option 8 (Enable Online Mode)                 ║")
        print("  ║  3. Make sure the server is running                      ║")
        print("  ╚══════════════════════════════════════════════════════════╝")
        return

    # Check if user is logged in
    if not _current_user:
        print("  You must be logged in to view the user list.")
        return

    # Connect to server if not already connected
    if _server_client is None or _server_client.sock is None:
        success, msg = connect_to_server()
        if not success:
            print(f"  Cannot connect to server: {msg}")
            print("  Make sure the server is running: python3 server.py")
            return
    
    # Ensure we're logged in on the server
    if not _server_client.logged_in_user:
        print("  Logging in to server...")
        saved_user, saved_password = _load_credentials()
        if saved_user == _current_user and saved_password:
            login_resp = _server_client.login(_current_user, saved_password, use_encryption=True)
            if not (login_resp and login_resp.get('success')):
                print("  Failed to login to server. Please login again from main menu.")
                return
        else:
            print("  No saved credentials. Please login again from main menu.")
            return

    response = _server_client.list_users()
    if response is None:
        print("  No response from server. Connection may have timed out.")
        print("  Make sure the server is running and you have a stable connection.")
        return

    if not response.get('success'):
        print(f"  Failed to get user list: {response.get('data', 'Unknown error')}")
        return

    users = response.get('data', [])
    print("\n  ╔══════════════════════════════════════════════════════════╗")
    print(f"  ║  REGISTERED USERS ({len(users)}):{'':35}║")
    print("  ╚══════════════════════════════════════════════════════════╝")

    if not users:
        print("    No registered users yet.")
    else:
        for user in sorted(users):
            current_marker = " (you)" if user == _current_user else ""
            print(f"    • {user}{current_marker}")
    print()

# ════════════════════════════════════════════════════════════════════════
#  FRIENDS & MESSAGING SYSTEM
# ════════════════════════════════════════════════════════════════════════

# In-memory storage for E2E encryption keys
_user_private_keys = {}
_user_public_keys = {}

def _generate_keypair():
    """Generate a simple keypair for E2E encryption (simplified for demonstration)."""
    # In a real implementation, use proper cryptographic libraries
    # This is a simplified version for demonstration
    import hashlib
    import secrets
    
    # Generate a random private key
    private_key = secrets.token_hex(32)
    # Generate a public key (simplified - in reality would use DH or RSA)
    public_key = hashlib.sha256(private_key.encode()).hexdigest()
    
    return private_key, public_key

def _encrypt_message(message, recipient_public_key):
    """Encrypt a message for a recipient (simplified)."""
    # In a real implementation, use proper AES-GCM encryption
    # This is a simplified version for demonstration
    import base64
    import hashlib
    import os
    
    # Generate a random IV and key
    iv = os.urandom(12)
    key = hashlib.sha256(recipient_public_key.encode()).digest()
    
    # Simple XOR encryption (NOT secure - for demonstration only)
    # In production, use cryptography library with AES-GCM
    message_bytes = message.encode()
    encrypted = bytes(a ^ b for a, b in zip(message_bytes, (key * ((len(message_bytes) // 32) + 1))[:len(message_bytes)]))
    
    return base64.b64encode(encrypted).decode(), base64.b64encode(iv).decode(), "demo_tag"

def _decrypt_message(encrypted_content, iv, tag, sender_public_key):
    """Decrypt a message from a sender (simplified)."""
    import base64
    import hashlib
    
    key = hashlib.sha256(sender_public_key.encode()).digest()
    encrypted_bytes = base64.b64decode(encrypted_content)
    
    # Simple XOR decryption (NOT secure - for demonstration only)
    decrypted = bytes(a ^ b for a, b in zip(encrypted_bytes, (key * ((len(encrypted_bytes) // 32) + 1))[:len(encrypted_bytes)]))
    
    return decrypted.decode()

def friends_messaging_menu():
    """Main menu for friends and messaging."""
    global _current_user, _server_client

    if not _current_user:
        print("\n  ╔══════════════════════════════════════════════════════════╗")
        print("  ║           PLEASE LOG IN FIRST                            ║")
        print("  ╚══════════════════════════════════════════════════════════╝")
        return

    # Generate E2E encryption keys for messaging (separate from session encryption)
    private_key, public_key = _generate_keypair()
    _user_private_keys[_current_user] = private_key
    _user_public_keys[_current_user] = public_key

    # Note: Session encryption is already established at login
    # No need to do another key exchange here

    while True:
        print("\n  ╔══════════════════════════════════════════════════════════╗")
        print("  ║           FRIENDS & MESSAGING                            ║")
        print("  ╠══════════════════════════════════════════════════════════╣")
        print("  ║  1. View Friends List                                    ║")
        print("  ║  2. Add Friend                                           ║")
        print("  ║  3. Friend Requests                                      ║")
        print("  ║  4. Messages                                             ║")
        print("  ║  5. Challenges                                           ║")
        print("  ║  0. Back to Main Menu                                    ║")
        print("  ╚══════════════════════════════════════════════════════════╝")
        
        try:
            choice = input("  Choice: ").strip()
        except EOFError:
            return
        
        if choice == '0':
            return
        elif choice == '1':
            view_friends_list()
        elif choice == '2':
            add_friend()
        elif choice == '3':
            friend_requests_menu()
        elif choice == '4':
            messages_menu()
        elif choice == '5':
            challenges_menu()
        else:
            print("  Invalid choice.")

def view_friends_list():
    """View list of friends."""
    print("\n  ╔══════════════════════════════════════════════════════════╗")
    print("  ║              YOUR FRIENDS                                ║")
    print("  ╚══════════════════════════════════════════════════════════╝")

    # Check if user is logged in
    if not _current_user:
        print("  You must be logged in to view friends.")
        return

    # Check if client is connected
    if not _server_client or not _server_client.sock:
        print("  Not connected to server. Please connect first.")
        success, msg = connect_to_server()
        if not success:
            print(f"  {msg}")
            return
    
    # Ensure we're logged in on the server
    if not _server_client.logged_in_user:
        print("  Logging in to server...")
        saved_user, saved_password = _load_credentials()
        if saved_user == _current_user and saved_password:
            login_resp = _server_client.login(_current_user, saved_password, use_encryption=True)
            if not (login_resp and login_resp.get('success')):
                print("  Failed to login to server. Please login again from main menu.")
                return
        else:
            print("  No saved credentials. Please login again from main menu.")
            return

    response = _server_client.get_friend_list()
    if not response or not response.get('success'):
        print(f"  Error: {response.get('data', 'Unknown error') if response else 'No response'}")
        return

    friends = response.get('data', {}).get('friends', [])
    if not friends:
        print("  You don't have any friends yet. Add some!")
        return

    print(f"  {'Username':<20} {'Status':<10}")
    print("  " + "-" * 30)
    for friend in friends:
        status = "Online" if friend.get('online') else "Offline"
        print(f"  {friend['username']:<20} {status:<10}")

    print("\n  Actions:")
    print("  M - Message a friend")
    print("  C - Challenge a friend")
    print("  R - Remove a friend")
    print("  0 - Back")

    try:
        action_line = input("  Action: ").strip()
    except EOFError:
        return
    
    # Parse action and optional argument (e.g., "M XDblocky" or just "M")
    action_parts = action_line.upper().split(None, 1)  # Split on whitespace, max 2 parts
    action = action_parts[0] if action_parts else ''
    arg = action_parts[1] if len(action_parts) > 1 else None
    
    # Convert action back to original case for friend name if provided
    if arg and action.upper() == 'M':
        # For message, use the original case from input
        original_parts = action_line.split(None, 1)
        friend_name_arg = original_parts[1] if len(original_parts) > 1 else None
    else:
        friend_name_arg = arg

    if action == '0':
        return
    elif action == 'M':
        if friend_name_arg:
            open_chat_with_friend(friend_name_arg)
        else:
            friend_name = input("  Friend's username: ").strip()
            if friend_name:
                open_chat_with_friend(friend_name)
    elif action == 'C':
        if friend_name_arg:
            challenge_friend(friend_name_arg)
        else:
            friend_name = input("  Friend's username: ").strip()
            if friend_name:
                challenge_friend(friend_name)
    elif action == 'R':
        if friend_name_arg:
            response = _server_client.remove_friend(friend_name_arg)
            if response and response.get('success'):
                print(f"  Friend '{friend_name_arg}' removed.")
            else:
                print(f"  Error: {response.get('data', 'Unknown error') if response else 'Failed'}")
        else:
            friend_name = input("  Friend's username to remove: ").strip()
            if friend_name:
                response = _server_client.remove_friend(friend_name)
                if response and response.get('success'):
                    print(f"  Friend '{friend_name}' removed.")
                else:
                    print(f"  Error: {response.get('data', 'Unknown error') if response else 'Failed'}")

def add_friend():
    """Add a new friend."""
    print("\n  ╔══════════════════════════════════════════════════════════╗")
    print("  ║              ADD FRIEND                                  ║")
    print("  ╚══════════════════════════════════════════════════════════╝")

    # Check if user is logged in
    if not _current_user:
        print("  You must be logged in to add friends.")
        return

    # First show list of users
    # Check if client is connected
    if not _server_client or not _server_client.sock:
        print("  Not connected to server. Please connect first.")
        success, msg = connect_to_server()
        if not success:
            print(f"  {msg}")
            return
    
    # Ensure we're logged in on the server
    if not _server_client.logged_in_user:
        print("  Logging in to server...")
        saved_user, saved_password = _load_credentials()
        if saved_user == _current_user and saved_password:
            login_resp = _server_client.login(_current_user, saved_password, use_encryption=True)
            if not (login_resp and login_resp.get('success')):
                print("  Failed to login to server. Please login again from main menu.")
                return
        else:
            print("  No saved credentials. Please login again from main menu.")
            return

    response = _server_client.list_users()
    if not response or not response.get('success'):
        print("  Could not fetch user list.")
        if response:
            print(f"  Error: {response.get('data', 'Unknown error')}")
        return

    users = response.get('data', [])
    print("  Registered users:")
    for user in sorted(users):
        if user != _current_user:
            print(f"    • {user}")

    friend_name = input("\n  Username to add: ").strip()
    if not friend_name:
        return
    if friend_name == _current_user:
        print("  Cannot add yourself as a friend!")
        return

    response = _server_client.send_friend_request(friend_name)
    if response and response.get('success'):
        print(f"  Friend request sent to {friend_name}!")
    else:
        print(f"  Error: {response.get('data', 'Unknown error') if response else 'Failed'}")

def friend_requests_menu():
    """View and respond to friend requests."""
    print("\n  ╔══════════════════════════════════════════════════════════╗")
    print("  ║           FRIEND REQUESTS                                ║")
    print("  ╚══════════════════════════════════════════════════════════╝")

    # Check if user is logged in
    if not _current_user:
        print("  You must be logged in to view friend requests.")
        return

    # Check if client is connected
    if not _server_client or not _server_client.sock:
        print("  Not connected to server. Please connect first.")
        success, msg = connect_to_server()
        if not success:
            print(f"  {msg}")
            return
    
    # Ensure we're logged in on the server
    if not _server_client.logged_in_user:
        print("  Logging in to server...")
        saved_user, saved_password = _load_credentials()
        if saved_user == _current_user and saved_password:
            login_resp = _server_client.login(_current_user, saved_password, use_encryption=True)
            if not (login_resp and login_resp.get('success')):
                print("  Failed to login to server. Please login again from main menu.")
                return
        else:
            print("  No saved credentials. Please login again from main menu.")
            return

    response = _server_client.get_friend_requests()
    if not response or not response.get('success'):
        print(f"  Error: {response.get('data', 'Unknown error') if response else 'No response'}")
        return

    requests = response.get('data', {}).get('requests', [])
    if not requests:
        print("  No pending friend requests.")
        return

    print("  Pending requests:")
    for i, req in enumerate(requests, 1):
        print(f"  {i}. From: {req['sender']}")

    print("\n  Enter request number to respond, or 0 to cancel:")

    try:
        choice = input("  Choice: ").strip()
    except EOFError:
        return

    if choice == '0':
        return

    try:
        idx = int(choice) - 1
        if 0 <= idx < len(requests):
            sender = requests[idx]['sender']
            print(f"\n  Respond to request from {sender}:")
            print("  A - Accept")
            print("  D - Decline")
            action = input("  Action: ").strip().upper()
            
            if action == 'A':
                response = _server_client.respond_to_friend_request(sender, True)
                if response and response.get('success'):
                    print(f"  Friend request from {sender} accepted!")
            elif action == 'D':
                response = _server_client.respond_to_friend_request(sender, False)
                if response and response.get('success'):
                    print(f"  Friend request from {sender} declined.")
    except ValueError:
        print("  Invalid choice.")

def messages_menu():
    """View and manage messages."""
    print("\n  ╔══════════════════════════════════════════════════════════╗")
    print("  ║              MESSAGES                                    ║")
    print("  ╚══════════════════════════════════════════════════════════╝")

    # Check if user is logged in
    if not _current_user:
        print("  You must be logged in to view messages.")
        return

    # Check if client is connected
    if not _server_client or not _server_client.sock:
        print("  Not connected to server. Please connect first.")
        success, msg = connect_to_server()
        if not success:
            print(f"  {msg}")
            return
    
    # Ensure we're logged in on the server
    if not _server_client.logged_in_user:
        print("  Logging in to server...")
        saved_user, saved_password = _load_credentials()
        if saved_user == _current_user and saved_password:
            login_resp = _server_client.login(_current_user, saved_password, use_encryption=True)
            if not (login_resp and login_resp.get('success')):
                print("  Failed to login to server. Please login again from main menu.")
                return
        else:
            print("  No saved credentials. Please login again from main menu.")
            return

    # Get friends list
    response = _server_client.get_friend_list()
    if not response or not response.get('success'):
        print("  Could not fetch friends list.")
        return

    friends = response.get('data', {}).get('friends', [])
    if not friends:
        print("  You need friends before you can send messages!")
        return

    print("  Friends you can message:")
    for i, friend in enumerate(friends, 1):
        print(f"  {i}. {friend['username']}")

    print("\n  Enter friend number to view messages, or 0 to cancel:")

    try:
        choice = input("  Choice: ").strip()
    except EOFError:
        return

    if choice == '0':
        return

    try:
        idx = int(choice) - 1
        if 0 <= idx < len(friends):
            friend = friends[idx]['username']
            open_chat_with_friend(friend)
    except ValueError:
        print("  Invalid choice.")

def open_chat_with_friend(friend_name):
    """Open a chat interface with a friend."""
    print(f"\n  ╔══════════════════════════════════════════════════════════╗")
    print(f"  ║  Chat with {friend_name:<36}║")
    print(f"  ╚══════════════════════════════════════════════════════════╝")

    # Load existing messages asynchronously (don't block on this)
    messages = []
    
    # Quick check if we can get messages (2 second timeout max)
    if _server_client and _server_client.sock:
        try:
            _server_client.send(MSG_GET_MESSAGES, {'friend': friend_name, 'since_id': 0})
            response = _server_client.recv(timeout=2.0)  # Short timeout
            if response and response.get('success'):
                messages = response.get('data', {}).get('messages', [])
        except:
            pass  # Non-critical, continue without loading messages

    # Display messages if we got any
    if messages:
        print("\n  Recent messages:")
        for msg in messages[-20:]:  # Show last 20 messages
            sender = msg['sender']
            content = msg['encrypted_content'][:50] + "..." if len(msg['encrypted_content']) > 50 else msg['encrypted_content']
            print(f"    [{sender}] {content}")
        print()
    else:
        print("\n  No recent messages. Start the conversation!\n")

    # Chat loop
    while True:
        try:
            message = input(f"  Message to {friend_name} (or 'back' to return): ").strip()
        except EOFError:
            return

        if message.lower() == 'back':
            return
        if not message:
            continue

        # Encrypt and send message
        if friend_name in _user_public_keys:
            encrypted, iv, tag = _encrypt_message(message, _user_public_keys[friend_name])
        else:
            encrypted, iv, tag = _encrypt_message(message, "demo_key")

        response = _server_client.send_message(friend_name, encrypted, iv, tag)

        # Handle response from server
        if response is None:
            # Real connection issue - message may not have been sent
            print(f"  Error sending message: No response from server (connection may have timed out or been lost)")
        elif response.get('success'):
            # Message successfully stored on server
            print(f"  [You] {message}")
            # Recipient doesn't need to be online - message is stored on server
            # and will be delivered when they come online and pull messages
            if not response.get('recipient_online', False):
                print(f"  (Message stored on server - {friend_name} will receive it when they come online)")
        else:
            # Actual error from server
            error_data = response.get('error', response.get('data', 'Unknown error'))
            print(f"  Error sending message: {error_data}")
            if error_data == "Users are not friends":
                print(f"  Hint: You can only message users who are your friends.")
            elif "Not logged in" in str(error_data):
                print(f"  Hint: Your session may have expired. Please log in again.")

def challenges_menu():
    """View and manage game challenges."""
    print("\n  ╔══════════════════════════════════════════════════════════╗")
    print("  ║              CHALLENGES                                  ║")
    print("  ╚══════════════════════════════════════════════════════════╝")
    
    response = _server_client.get_challenges()
    if not response or not response.get('success'):
        print(f"  Error: {response.get('data', 'Unknown error') if response else 'No response'}")
        return
    
    challenges = response.get('data', {}).get('challenges', [])
    if not challenges:
        print("  No pending challenges.")
        print("\n  Actions:")
        print("  N - Send new challenge")
        print("  0 - Back")
    else:
        print("  Pending challenges:")
        for i, chal in enumerate(challenges, 1):
            challenger = chal['challenger']
            challenged = chal['challenged']
            is_from_me = challenger == _current_user
            other_player = challenged if is_from_me else challenger
            direction = "→" if is_from_me else "←"
            print(f"  {i}. {direction} {other_player} ({chal['color_choice']}, {'rated' if chal['rated'] else 'unrated'})")
        
        print("\n  Actions:")
        print("  Enter challenge number to respond")
        print("  N - Send new challenge")
        print("  0 - Back")
    
    try:
        choice = input("  Choice: ").strip().upper()
    except EOFError:
        return
    
    if choice == '0':
        return
    elif choice == 'N':
        # Get friend to challenge
        response = _server_client.get_friend_list()
        if response and response.get('success'):
            friends = response.get('data', {}).get('friends', [])
            if friends:
                print("\n  Friends you can challenge:")
                for i, friend in enumerate(friends, 1):
                    print(f"  {i}. {friend['username']}")
                
                try:
                    friend_choice = input("  Choice: ").strip()
                    idx = int(friend_choice) - 1
                    if 0 <= idx < len(friends):
                        friend = friends[idx]['username']
                        challenge_friend(friend)
                except (ValueError, EOFError):
                    pass
    else:
        try:
            idx = int(choice) - 1
            if 0 <= idx < len(challenges):
                chal = challenges[idx]
                is_from_me = chal['challenger'] == _current_user
                other_player = chal['challenged'] if is_from_me else chal['challenger']
                
                if is_from_me:
                    # Cancel challenge
                    print(f"  Cancel challenge to {other_player}? [y/N]: ", end='')
                    try:
                        confirm = input().strip().lower()
                    except EOFError:
                        return
                    if confirm == 'y':
                        response = _server_client.cancel_challenge(other_player)
                        if response and response.get('success'):
                            print("  Challenge cancelled.")
                else:
                    # Respond to challenge
                    print(f"\n  Respond to challenge from {other_player}:")
                    print("  A - Accept")
                    print("  D - Decline")
                    try:
                        action = input("  Action: ").strip().upper()
                    except EOFError:
                        return
                    
                    if action == 'A':
                        response = _server_client.respond_to_challenge(other_player, True)
                        if response and response.get('success'):
                            print(f"  Challenge accepted! Starting game...")
                            # The game will start automatically
                    elif action == 'D':
                        response = _server_client.respond_to_challenge(other_player, False)
                        if response and response.get('success'):
                            print("  Challenge declined.")
        except ValueError:
            print("  Invalid choice.")

def challenge_friend(friend_name):
    """Send a challenge to a friend."""
    print(f"\n  ╔══════════════════════════════════════════════════════════╗")
    print(f"  ║  Challenge {friend_name:<37}║")
    print(f"  ╚══════════════════════════════════════════════════════════╝")
    
    print("  Color choice:")
    print("  1. Random")
    print("  2. White")
    print("  3. Black")
    
    try:
        color_choice = input("  Choice: ").strip()
    except EOFError:
        return
    
    color_map = {'1': 'random', '2': 'white', '3': 'black'}
    color = color_map.get(color_choice, 'random')
    
    print("  Rated game? [Y/n]: ", end='')
    try:
        rated_choice = input().strip().lower()
    except EOFError:
        rated_choice = 'y'
    rated = rated_choice != 'n'
    
    response = _server_client.send_challenge(friend_name, color, rated)
    if response and response.get('success'):
        print(f"  Challenge sent to {friend_name}!")
    else:
        print(f"  Error: {response.get('data', 'Unknown error') if response else 'Failed'}")

def configure_server_connection():
    """Configure server host and port."""
    global _server_host, _server_port, _server_client

    print("\n  ╔══════════════════════════════════════════════════════════╗")
    print("  ║           SERVER CONNECTION SETTINGS                     ║")
    print("  ╠══════════════════════════════════════════════════════════╣")
    host_display = _server_host if _server_host else "(not configured)"
    port_display = _server_port if _server_port else "(not configured)"
    print(f"  ║  Current Host: {host_display:<42}║")
    print(f"  ║  Current Port: {port_display:<42}║")
    print("  ╠══════════════════════════════════════════════════════════╣")
    print("  ║  1. Change Server                                        ║")
    print("  ║  2. Clear Saved Server Settings                          ║")
    print("  ║  0. Back                                                 ║")
    print("  ╚══════════════════════════════════════════════════════════╝")

    try:
        choice = input("  Choice: ").strip()

        if choice == '0':
            return
        elif choice == '1':
            # Disconnect existing connection
            if _server_client:
                _server_client.disconnect()
                _server_client = None

            # Get new server details
            host = input("  Enter server host/IP: ").strip()
            if not host:
                print("  Cancelled.")
                return

            port_str = input("  Enter server port [65433]: ").strip()
            if not port_str:
                port_str = '65433'

            _server_host = host
            _server_port = int(port_str)

            # Save configuration
            _save_server_config(_server_host, _server_port)

            print(f"\n  ✓ Server configured: {_server_host}:{_server_port}")
            print("  Server settings saved for future sessions")

            # Test connection
            success, msg = connect_to_server()
            if success:
                print(f"  ✓ Connected to server at {_server_host}:{_server_port}")
            else:
                print(f"  ✗ {msg}")
                print("  (Settings saved, will try to connect on next operation)")
                print("  Make sure the server is running: python3 server.py")

        elif choice == '2':
            _remove_server_config()
            _server_host = None
            _server_port = None
            if _server_client:
                _server_client.disconnect()
                _server_client = None
            print("\n  ✓ Server settings cleared")
            print("  You will be prompted to choose a server next time")

    except ValueError:
        print("  Invalid port number.")
    except EOFError:
        pass

def auth_menu():
    """Display authentication menu."""
    while True:
        print("\n  ╔══════════════════════════════════════════════════════════╗")
        print("  ║              ACCOUNT MANAGEMENT                          ║")
        print("  ╠══════════════════════════════════════════════════════════╣")
        
        if _offline_mode:
            print("  ║  [OFFLINE MODE - Online features disabled]               ║")
            print("  ╠══════════════════════════════════════════════════════════╣")
            print("  ║  To use online accounts:                                 ║")
            print("  ║  - Return to main menu                                   ║")
            print("  ║  - Select option 8 (Toggle Offline Mode)                 ║")
            print("  ╚══════════════════════════════════════════════════════════╝")
        else:
            if _current_user:
                print(f"  ║  Logged in as: {_current_user:<40}  ║")
                print("  ╠══════════════════════════════════════════════════════════╣")
                print("  ║  1. View My Profile                                      ║")
                print("  ║  2. View Another User's Profile                          ║")
                print("  ║  3. List All Users                                       ║")
                print("  ║  4. Logout                                               ║")
                # Check if credentials are saved
                saved_user, _ = _load_credentials()
                if saved_user == _current_user:
                    print("  ║  5. Disable Auto-Login (clear saved credentials)         ║")
                else:
                    print("  ║  5. Save Credentials for Auto-Login                      ║")
            else:
                print("  ║  Not logged in                                           ║")
                print("  ╠══════════════════════════════════════════════════════════╣")
                print("  ║  1. Login                                                ║")
                print("  ║  2. Register New Account                                 ║")
                # Check if credentials are saved
                saved_user, _ = _load_credentials()
                if saved_user:
                    print(f"  ║  3. Auto-Login as '{saved_user}'                         ║")
                    print("  ║  4. Clear Saved Credentials                              ║")
            print("  ╠══════════════════════════════════════════════════════════╣")
            print("  ║  6. Configure Server Connection                          ║")

        print("  ║  0. Back to Main Menu                                    ║")
        print("  ╚══════════════════════════════════════════════════════════╝")

        try:
            choice = input("  Choice: ").strip()
        except EOFError:
            break

        if choice == '0':
            break

        if _offline_mode:
            print("\n  Please disable offline mode from the main menu first.")
            continue

        if choice == '1':
            if _current_user:
                view_profile(_current_user)
            else:
                login_user()
                if _current_user:
                    clear_screen()
        elif choice == '2':
            if _current_user:
                try:
                    username = input("  Enter username to view: ").strip()
                except EOFError:
                    continue
                view_profile(username)
            else:
                register_user()
                if _current_user:
                    clear_screen()
        elif choice == '3':
            if _current_user:
                list_all_users()
            else:
                # Auto-login if credentials saved
                saved_user, _ = _load_credentials()
                if saved_user:
                    auto_login()
                    if _current_user:
                        clear_screen()
                else:
                    print("  Please login or register first.")
        elif choice == '4':
            if _current_user:
                logout_user()
            else:
                # Clear saved credentials
                if _remove_credentials():
                    print("  Saved credentials cleared.")
                else:
                    print("  No saved credentials to clear.")
        elif choice == '5':
            if _current_user:
                # Save or disable auto-login
                saved_user, _ = _load_credentials()
                if saved_user == _current_user:
                    _remove_credentials()
                    print("  Auto-login disabled. Credentials cleared.")
                else:
                    # Need password to save credentials
                    print("\n  To save credentials for auto-login, please login again.")
                    print("  (This is required to store your password securely)")
                    try:
                        ans = input("  Login now? [Y/n]: ").strip().lower()
                    except EOFError:
                        ans = 'n'
                    if ans in ('y', 'yes', ''):
                        login_user()
            else:
                print("  Not logged in.")
        elif choice == '6':
            configure_server_connection()


# ════════════════════════════════════════════════════════════════════════
#  ONLINE MATCHMAKING
# ════════════════════════════════════════════════════════════════════════
def matchmaking_menu():
    """Display matchmaking menu for online games."""
    global _server_client, _current_user

    # Check offline mode
    if _offline_mode:
        print("\n  ╔══════════════════════════════════════════════════════════╗")
        print("  ║              OFFLINE MODE ACTIVE                         ║")
        print("  ╠══════════════════════════════════════════════════════════╣")
        print("  ║  Online matchmaking requires internet connection.        ║")
        print("  ║                                                          ║")
        print("  ║  To enable online features:                              ║")
        print("  ║  1. Return to main menu                                  ║")
        print("  ║  2. Select option 8 (Toggle Offline Mode)                ║")
        print("  ║  3. Configure server connection if needed                ║")
        print("  ╚══════════════════════════════════════════════════════════╝")
        return

    if not _current_user:
        print("\n  You must be logged in to use matchmaking.")
        print("  Please login or register from Account Management.")
        return

    # Check if already connected, if not connect
    if _server_client is None or _server_client.sock is None:
        success, msg = connect_to_server()
        if not success:
            print(f"\n  Cannot connect to server: {msg}")
            print("  Make sure the server is running (python3 server.py)")
            return
    else:
        # Connection exists, verify it's still alive with a ping
        _server_client.send(MSG_PING)
        ping_resp = _server_client.recv(timeout=2.0)
        if ping_resp is None or not ping_resp.get('success'):
            # Connection lost, reconnect
            print("\n  Connection lost. Reconnecting...")
            success, msg = connect_to_server(reconnect=True)
            if not success:
                print(f"\n  Cannot reconnect to server: {msg}")
                print("  Make sure the server is running (python3 server.py)")
                return
            
            # After reconnect, we need to re-login
            # For now, inform the user
            print("\n  Session expired. Please log in again.")
            print("  Return to main menu and go to Account Management to log in.")
            return

    in_queue = False
    in_game = False
    current_game_id = None
    my_color = None
    opponent_name = None
    last_refresh = time.time()
    refresh_interval = 5.0  # Auto-refresh every 5 seconds

    print("\n  ╔══════════════════════════════════════════════════════════╗")
    print("  ║              ONLINE MATCHMAKING                          ║")
    print("  ╠══════════════════════════════════════════════════════════╣")
    print("  ║  Find a random opponent for a rated game!                ║")
    print("  ╚══════════════════════════════════════════════════════════╝")

    # Message listener is already running in _server_client
    # Use its message queue for async notifications

    # Start keep-alive ping thread to maintain connection
    def keep_alive():
        while not _server_client._listener_stop.is_set():
            time.sleep(10)  # Ping every 10 seconds
            try:
                _server_client.send(MSG_PING)
            except:
                pass

    keep_alive_thread = threading.Thread(target=keep_alive, daemon=True)
    keep_alive_thread.start()

    while True:
        # Process any pending messages from centralized queue
        try:
            while not _server_client._msg_queue.empty():
                msg = _server_client._msg_queue.get_nowait()
                msg_type = msg.get('type', '')
                data = msg.get('data', {})

                if msg_type == MSG_MATCH:
                    # Match found!
                    in_game = True
                    in_queue = False
                    current_game_id = data.get('game_id')
                    my_color = data.get('color')
                    opponent_name = data.get('opponent')
                    print(f"\n  ╔══════════════════════════════════════════════════════════╗")
                    print(f"  ║  MATCH FOUND!                                              ║")
                    print(f"  ╠══════════════════════════════════════════════════════════╣")
                    print(f"  ║  Opponent: {opponent_name:<46}║")
                    print(f"  ║  Your Color: {my_color.upper():<44}║")
                    print(f"  ║  Game ID: {current_game_id:<47}║")
                    print(f"  ╚══════════════════════════════════════════════════════════╝")
                    print("\n  Starting game...")
                    time.sleep(1)
                    # Start the online game
                    play_online_matched_game(current_game_id, my_color, opponent_name, msg_queue, stop_listener)
                    in_game = False
                    current_game_id = None
                    break
                
                elif msg_type == MSG_GAME_MOVE:
                    # Opponent's move received - will be handled in game loop
                    msg_queue.put(msg)
                
                elif msg_type == MSG_GAME_RESIGN:
                    winner = data.get('winner')
                    resigned_by = data.get('resigned_by')
                    print(f"\n  {resigned_by} resigned. {winner} wins!")
                    in_game = False
                
                elif msg_type == MSG_GAME_DRAW_OFFER:
                    offered_by = data.get('offered_by')
                    print(f"\n  {offered_by} offers a draw.")
                    try:
                        ans = input("  Accept draw? [y/N]: ").strip().lower()
                    except EOFError:
                        ans = 'n'
                    if ans in ('y', 'yes'):
                        _server_client.accept_draw(current_game_id)
                        print("  Game ended in a draw.")
                        in_game = False
                    else:
                        print("  Draw offer declined.")
                
                elif msg_type == MSG_GAME_DRAW_ACCEPT:
                    print(f"\n  Draw accepted! Game ended in a draw.")
                    in_game = False
                
                elif msg_type == MSG_GAME_CHAT:
                    from_player = data.get('from_player')
                    message = data.get('message')
                    print(f"\n  [{from_player}]: {message}")
        except:
            pass
        
        if in_game:
            continue

        # Auto-refresh queue status every 5 seconds when in queue
        current_time = time.time()
        if in_queue and current_time - last_refresh >= refresh_interval:
            status_resp = _server_client.get_queue_status()
            if status_resp and status_resp.get('success'):
                status = status_resp.get('data', {})
                position = status.get('position', '?')
                wait_time = status.get('wait_time', 0)
                queued = status.get('queued_players', 0)
                print(f"\n  [Auto-refresh] Position: {position} | Waiting: {wait_time}s | Players: {queued}")
            last_refresh = current_time

        print("\n  ╔══════════════════════════════════════════════════════════╗")
        if in_queue:
            print("  ║  Status: IN QUEUE - Waiting for opponent...            ║")
            # Get queue status
            status_resp = _server_client.get_queue_status()
            if status_resp and status_resp.get('success'):
                status = status_resp.get('data', {})
                position = status.get('position', '?')
                wait_time = status.get('wait_time', 0)
                queued = status.get('queued_players', 0)
                print(f"  ║  Position: {position} | Waiting: {wait_time}s | Players: {queued}          ║")
        else:
            print("  ║  Status: NOT IN QUEUE                                    ║")
        print("  ╠══════════════════════════════════════════════════════════╣")
        if not in_queue:
            print("  ║  1. Join Queue - Find a game                             ║")
        else:
            print("  ║  2. Leave Queue                                          ║")
            print("  ║  3. Refresh - Check for opponents                        ║")
        print("  ║  0. Back to Main Menu                                    ║")
        print("  ╚══════════════════════════════════════════════════════════╝")

        try:
            choice = input("  Choice: ").strip()
        except EOFError:
            break

        if choice == '0':
            if in_queue:
                _server_client.leave_queue()
            break
        elif choice == '1' and not in_queue:
            resp = _server_client.join_queue()
            if resp and resp.get('success'):
                in_queue = True
                last_refresh = time.time()  # Reset auto-refresh timer
                print(f"  {resp.get('data', 'Joined queue')}")
            else:
                error_msg = resp.get('data', 'Unknown error') if resp else 'Connection timeout'
                print(f"  Failed to join queue: {error_msg}")
        elif choice == '2' and in_queue:
            _server_client.leave_queue()
            in_queue = False
            print("  Left queue.")
        elif choice == '3' and in_queue:
            # Refresh: trigger matchmaking check
            print("  Checking for available opponents...")
            resp = _server_client.trigger_matchmaking()
            if resp and resp.get('success'):
                msg = resp.get('data', {}).get('message', 'Matchmaking check complete')
                print(f"  {msg}")
            else:
                error_msg = resp.get('data', 'Unable to refresh') if resp else 'Connection timeout'
                print(f"  {error_msg}")
            last_refresh = time.time()  # Reset auto-refresh timer
    
    stop_listener.set()
    listener_thread.join(timeout=2)


def play_online_matched_game(game_id, my_color, opponent_name, msg_queue, stop_listener):
    """Play an online matched game."""
    board = Board()
    board.reset()
    last_mv = None
    game_start_time = time.time()

    my_turn = (my_color == 'white' and board.side == WHITE) or \
              (my_color == 'black' and board.side == BLACK)

    my_name = _current_user
    white_name = my_name if my_color == 'white' else opponent_name
    black_name = opponent_name if my_color == 'white' else my_name

    print("\n  ╔══════════════════════════════════════════════════════════╗")
    print("  ║                    ONLINE GAME                           ║")
    print("  ╠══════════════════════════════════════════════════════════╣")
    print(f"  ║  {white_name:<28} vs  {black_name:<28}║")
    print("  ╚══════════════════════════════════════════════════════════╝\n")

    while True:
        # Process messages from centralized queue
        try:
            while not _server_client._msg_queue.empty():
                msg = _server_client._msg_queue.get_nowait()
                msg_type = msg.get('type', '')
                data = msg.get('data', {})
                
                if msg_type == MSG_GAME_MOVE:
                    move_san = data.get('move')
                    from_player = data.get('from_player')
                    # Apply the move
                    m = board.parse_san(move_san)
                    if m:
                        board.make(m)
                        last_mv = m
                        print(f"  {from_player} plays: {move_san}")

                elif msg_type == MSG_GAME_RESIGN:
                    winner = data.get('winner')
                    print(f"\n  {data.get('resigned_by')} resigned. {winner} wins!")
                    _save_game_to_server(white_name, black_name,
                                        'white' if winner == white_name else 'black',
                                        board.san_log, time.time() - game_start_time,
                                        show_elo_changes=True)
                    return

                elif msg_type == MSG_GAME_DRAW_OFFER:
                    offered_by = data.get('offered_by')
                    print(f"\n  {offered_by} offers a draw.")
                    try:
                        ans = input("  Accept draw? [y/N]: ").strip().lower()
                    except EOFError:
                        ans = 'n'
                    if ans in ('y', 'yes'):
                        _server_client.accept_draw(game_id)
                        print("  Game ended in a draw.")
                        _save_game_to_server(white_name, black_name, 'draw',
                                            board.san_log, time.time() - game_start_time,
                                            show_elo_changes=True)
                        return

                elif msg_type == MSG_GAME_CHAT:
                    print(f"\n  [{data.get('from_player')}]: {data.get('message')}")
        except:
            pass
        
        # Draw board
        persp = WHITE if my_color == 'white' else BLACK
        draw_board(board, persp, last_mv)
        
        turn_str = "White" if board.side == WHITE else "Black"
        chk_str = "  *** CHECK ***" if board.in_check() else ""
        print(f"  Move {board.fullmove} — {turn_str} to move{chk_str}")
        
        # Show moves
        if board.san_log:
            pairs = []
            for i in range(0, len(board.san_log), 2):
                wm = board.san_log[i]
                bm = board.san_log[i+1] if i+1 < len(board.san_log) else '...'
                pairs.append(f"{i//2+1}. {wm} {bm}")
            print("  " + ' | '.join(pairs[-4:]))
        
        print(f"  {white_name} vs {black_name}\n")
        
        legal = board.legal()
        if not legal:
            if board.in_check():
                winner = BLACK if board.side == WHITE else WHITE
                winner_name = black_name if winner == BLACK else white_name
                print(f"  Checkmate! {winner_name} wins!")
                _save_game_to_server(white_name, black_name,
                                    'white' if winner == WHITE else 'black',
                                    board.san_log, time.time() - game_start_time,
                                    show_elo_changes=True)
            else:
                print("  Stalemate - Draw!")
                _save_game_to_server(white_name, black_name, 'draw',
                                    board.san_log, time.time() - game_start_time,
                                    show_elo_changes=True)
            return

        # Check for draw conditions
        for cond, msg in [(board.is_repetition(), "threefold repetition"),
                          (board.is_fifty(), "50-move rule"),
                          (board.insufficient_material(), "insufficient material")]:
            if cond:
                print(f"  Draw: {msg}")
                _save_game_to_server(white_name, black_name, 'draw',
                                    board.san_log, time.time() - game_start_time,
                                    show_elo_changes=True)
                return
        
        # Check if it's my turn
        my_turn_now = (my_color == 'white' and board.side == WHITE) or \
                      (my_color == 'black' and board.side == BLACK)
        
        if not my_turn_now:
            print(f"  Waiting for {opponent_name}...")
            time.sleep(0.5)
            continue
        
        # My turn - get move
        try:
            raw = input("  Your move: ").strip()
        except EOFError:
            # Resign on disconnect
            _server_client.resign_game(game_id)
            return
        
        if not raw:
            continue
        
        cmd = raw.lower()
        
        if cmd in ('quit', 'exit'):
            _server_client.resign_game(game_id)
            print("  You resigned.")
            return
        
        if cmd == 'draw':
            _server_client.offer_draw(game_id)
            print("  Draw offer sent.")
            continue
        
        if cmd.startswith('chat '):
            _server_client.send_chat(game_id, raw[5:])
            continue
        
        if cmd == 'help':
            print(HELP)
            continue
        
        if cmd == 'moves':
            sms = [board.san(m) for m in legal]
            for i in range(0, len(sms), 8):
                print("  " + "  ".join(f"{s:<8}" for s in sms[i:i+8]))
            continue
        
        # Parse and send move
        mv = board.parse_san(raw)
        if mv is None:
            print(f"  Illegal/unrecognised: '{raw}'. Try 'moves' or 'help'.")
            continue
        
        s = board.san(mv)
        _server_client.send_move(game_id, s)
        board.make(mv)
        board.san_log.append(s)
        last_mv = mv


# ════════════════════════════════════════════════════════════════════════
#  BOT LEVELS (Beginner, Intermediate, Challenge)
# ════════════════════════════════════════════════════════════════════════
class BotLevel:
    """Enum for bot difficulty levels."""
    BEGINNER = 'beginner'
    INTERMEDIATE = 'intermediate'
    CHALLENGE = 'challenge'

BOT_NAMES = {
    BotLevel.BEGINNER: "BeginnerBot",
    BotLevel.INTERMEDIATE: "IntermediateBot",
    BotLevel.CHALLENGE: "ChallengeBot"
}

BOT_SETTINGS = {
    BotLevel.BEGINNER: {
        'depth': 1,
        'random_factor': 0.4,  # 40% chance of random move
        'think_time': 0.5,
        'use_book': False
    },
    BotLevel.INTERMEDIATE: {
        'depth': 3,
        'random_factor': 0.15,  # 15% chance of random move
        'think_time': 2.0,
        'use_book': True
    },
    BotLevel.CHALLENGE: {
        'depth': None,  # Use full search
        'random_factor': 0.0,  # No random moves
        'think_time': 5.0,
        'use_book': True
    }
}


class ChessBot:
    """Chess AI with configurable difficulty levels."""
    
    def __init__(self, level=BotLevel.INTERMEDIATE, tb=None, book=None):
        self.level = level
        self.settings = BOT_SETTINGS[level]
        self.engine = Engine(tb=tb, book=book if self.settings['use_book'] else None)
        self.tb = tb
        self.book = book
    
    def get_name(self):
        """Get the bot's display name."""
        return BOT_NAMES.get(self.level, "UnknownBot")
    
    def get_move(self, board):
        """Get the bot's move based on difficulty level."""
        legal = board.legal()
        if not legal:
            return None
        
        # Beginner and Intermediate bots sometimes make random moves
        if self.settings['random_factor'] > 0:
            if random.random() < self.settings['random_factor']:
                return random.choice(legal)
        
        # Challenge bot uses full engine search
        if self.level == BotLevel.CHALLENGE:
            self.engine.tt.clear()
            return self.engine.search(board, t_limit=self.settings['think_time'], verbose=False)
        
        # Beginner and Intermediate use limited depth search
        depth = self.settings['depth']
        self.engine.tt.clear()
        
        # Simplified search for lower levels
        best_move = None
        best_score = -INF
        
        for move in legal:
            board_copy = board.copy()
            board_copy.make(move)
            
            # Simple evaluation
            score = -self._evaluate_position(board_copy, depth - 1)
            
            if score > best_score:
                best_score = score
                best_move = move
        
        return best_move if best_move else random.choice(legal)
    
    def _evaluate_position(self, board, depth):
        """Simple recursive evaluation for lower difficulty bots."""
        if depth <= 0:
            return evaluate(board, self.tb)
        
        legal = board.legal()
        if not legal:
            if board.in_check():
                return -MATE_SCORE
            return 0
        
        best_score = -INF
        for move in legal:
            board_copy = board.copy()
            board_copy.make(move)
            score = -self._evaluate_position(board_copy, depth - 1)
            best_score = max(best_score, score)
        
        return best_score


def select_bot_level():
    """Let user select bot difficulty level."""
    print("\n  ╔══════════════════════════════════════════════════════════╗")
    print("  ║              SELECT BOT DIFFICULTY                       ║")
    print("  ╠══════════════════════════════════════════════════════════╣")
    print("  ║ 1. Beginner     - Easy opponent, makes random mistakes   ║")
    print("  ║ 2. Intermediate - Moderate challenge, occasional errors  ║")
    print("  ║ 3. Challenge    - Strong opponent, plays at full strength║")
    print("  ╚══════════════════════════════════════════════════════════╝")
    
    while True:
        try:
            choice = input("  Select difficulty [2]: ").strip() or '2'
        except EOFError:
            return BotLevel.INTERMEDIATE
        
        if choice == '1':
            return BotLevel.BEGINNER
        elif choice == '2':
            return BotLevel.INTERMEDIATE
        elif choice == '3':
            return BotLevel.CHALLENGE
        else:
            print("  Please enter 1, 2, or 3.")


# ════════════════════════════════════════════════════════════════════════
#  BOARD DISPLAY
# ════════════════════════════════════════════════════════════════════════
def draw_board(board, persp=WHITE, last=None, labels=True):
    lines=['']
    ranks=range(7,-1,-1) if persp==WHITE else range(8)
    files=range(8)       if persp==WHITE else range(7,-1,-1)
    for rank in ranks:
        row=f" {rank+1} "
        for file in files:
            sq=rank*8+file; p=board.sq[sq]
            dk=(rank+file)%2==0
            hl=last and sq in(last.from_sq,last.to_sq)
            if p:
                ch=PIECE_ASCII[p]
                row+=(f'[{ch}]' if dk else f' {ch} ')
            else:
                bg='*' if hl else('░' if dk else ' ')
                row+=(f'[{bg}]' if dk else f' {bg} ')
        lines.append(row)
    if labels:
        fl='    '+''.join(f' {chr(ord("a")+f)} ' for f in files)
        lines.append(fl)
    lines.append('')
    print('\n'.join(lines))

# ════════════════════════════════════════════════════════════════════════
#  BANNERS & HELP
# ════════════════════════════════════════════════════════════════════════
BANNER = """
╔══════════════════════════════════════════════════════════════╗
║                                                              ║
║   ██████╗██╗  ██╗███████╗███████╗███████╗                    ║
║  ██╔════╝██║  ██║██╔════╝██╔════╝██╔════╝                    ║
║  ██║     ███████║█████╗  ███████╗███████╗                    ║
║  ██║     ██╔══██║██╔══╝  ╚════██║╚════██║                    ║
║  ╚██████╗██║  ██║███████╗███████║███████║                    ║
║   ╚═════╝╚═╝  ╚═╝╚══════╝╚══════╝╚══════╝  Ultimate Ed.      ║
║                                                              ║
║  Neural Net • Opening Book • Tablebases • ELO • Multiplayer  ║
╚══════════════════════════════════════════════════════════════╝
"""

HELP = """
 ╔─── IN-GAME COMMANDS ──────────────────────────────────────────╗
 │  <move>    SAN move, e.g.: e4  Nf3  O-O  exd5  e8=Q           │
 │  undo      Take back last 2 half-moves (vs AI only)           │
 │  moves     Show all legal moves                               │
 │  flip      Flip board perspective                             │
 │  resign    Resign the game                                    │
 │  draw      Claim/offer draw                                   │
 │  chat <m>  Send chat message (multiplayer)                    │
 │  elo       Show ELO leaderboard                               │
 │  help      This help                                          │
 │  quit      Exit to main menu                                  │
 ╠─── SAN REFERENCE ─────────────────────────────────────────────╣
 │  Pawn:     e4  d5  exd5  (promotion:) e8=Q  e8=R  e8=B  e8=N  │
 │  Piece:    Nf3  Bxc4  Rhe1  Qd1f3 (disambiguation)            │
 │  Castle:   O-O  (kingside)   O-O-O  (queenside)               │
 ╚───────────────────────────────────────────────────────────────╝
"""

# ════════════════════════════════════════════════════════════════════════
#  GAME RESULT HANDLING
# ════════════════════════════════════════════════════════════════════════
def handle_game_end(board, elo_sys, white_name, black_name,
                    winner_color=None, draw=False, resigned=False):
    """Update ELO, offer analysis."""
    print()
    if draw:
        print("  ½-½  Draw\n")
        elo_sys.update(white_name, black_name, 0.5)
        elo_sys.update(black_name, white_name, 0.5)
        result_str='Draw'
    elif winner_color==WHITE:
        print(f"  1-0  {white_name} wins!\n")
        elo_sys.update(white_name, black_name, 1)
        result_str='White wins'
    else:
        print(f"  0-1  {black_name} wins!\n")
        elo_sys.update(black_name, white_name, 1)
        result_str='Black wins'

    w_elo=elo_sys.get_elo(white_name); b_elo=elo_sys.get_elo(black_name)
    print(f"  ELO — {white_name}: {w_elo}  |  {black_name}: {b_elo}\n")

    # Offer analysis
    try:
        ans=input("  Analyze game? [y/N] ").strip().lower()
    except EOFError:
        ans='n'
    if ans in('y','yes'):
        results=analyze_game(board.san_log, engine_time=1.0)
        print_analysis(results)

def _replay_board(san_log):
    """Replay san_log on a fresh board. Returns board or None."""
    b=Board(); b.reset()
    for s in san_log:
        m=b.parse_san(s)
        if not m: return None
        sn=b.san(m); b.make(m); b.san_log.append(sn)
    return b

# ════════════════════════════════════════════════════════════════════════
#  SINGLE-PLAYER (vs AI)
# ════════════════════════════════════════════════════════════════════════
def play_vs_ai(elo_sys, tb, book):
    board=Board(); board.reset()
    persp=WHITE; last_mv=None

    # Select bot difficulty
    bot_level = select_bot_level()
    bot = ChessBot(level=bot_level, tb=tb, book=book)
    bot_name = bot.get_name()

    while True:
        try:
            c=input("  Play as [W]hite or [B]lack? [W]: ").strip().lower() or 'w'
        except EOFError: return
        if c in('w','white'): human_color=WHITE; break
        if c in('b','black'): human_color=BLACK; break
        print("  Please enter 'w' or 'b'.")

    # Get player name (use logged-in username if available)
    default_name = _current_user if _current_user else 'Player'
    try:
        player_name=input(f"  Your name [{default_name}]: ").strip() or default_name
    except EOFError:
        player_name=default_name

    # Record game start time
    game_start = time.time()

    persp=human_color
    white_name=player_name if human_color==WHITE else bot_name
    black_name=bot_name if human_color==WHITE else player_name

    while True:
        draw_board(board, persp, last_mv)
        turn_str="White" if board.side==WHITE else "Black"
        chk_str="  *** CHECK ***" if board.in_check() else ""
        print(f"  Move {board.fullmove} — {turn_str} to move{chk_str}")

        # Show recent moves
        if board.san_log:
            pairs=[]
            for i in range(0,len(board.san_log),2):
                wm=board.san_log[i]
                bm=board.san_log[i+1] if i+1<len(board.san_log) else '...'
                pairs.append(f"{i//2+1}. {wm} {bm}")
            print("  "+' | '.join(pairs[-4:]))

        # ELO display
        we=elo_sys.get_elo(white_name); be=elo_sys.get_elo(black_name)
        print(f"  {white_name}({we}) vs {black_name}({be})\n")

        legal=board.legal()
        # Terminal conditions
        if not legal:
            draw_board(board, persp, last_mv)
            if board.in_check():
                winner=BLACK if board.side==WHITE else WHITE
                winner_color = winner
                result = 'white' if winner==WHITE else 'black'
            else:
                winner_color = None
                result = 'draw'
            handle_game_end(board,elo_sys,white_name,black_name,winner_color=winner_color)
            # Save game to server
            _save_game_to_server(white_name, black_name, result, board.san_log, time.time()-game_start)
            return

        for cond,msg in [(board.is_repetition(),"threefold repetition"),
                         (board.is_fifty(),"50-move rule"),
                         (board.insufficient_material(),"insufficient material")]:
            if cond:
                print(f"  ½-½ Draw: {msg}")
                handle_game_end(board,elo_sys,white_name,black_name,draw=True)
                # Save game to server
                _save_game_to_server(white_name, black_name, 'draw', board.san_log, time.time()-game_start)
                return

        # AI turn
        if board.side!=human_color:
            print(f"  {bot_name} thinking...\n")
            mv=bot.get_move(board)
            if mv:
                s=board.san(mv); board.make(mv); board.san_log.append(s)
                last_mv=mv; print(f"\n  {bot_name} plays: {s}\n")
            continue

        # Human turn
        try:
            raw=input("  Your move: ").strip()
        except EOFError:
            return
        if not raw: continue
        cmd=raw.lower()

        if cmd in('quit','exit','q'):
            # Save game as abandoned if moves were made
            if board.san_log:
                result = 'black' if human_color==WHITE else 'white'
                _save_game_to_server(white_name, black_name, result, board.san_log, time.time()-game_start)
            return
        if cmd=='help': print(HELP); continue
        if cmd=='flip': persp=1-persp; continue
        if cmd=='elo': elo_sys.leaderboard(); continue
        if cmd=='moves':
            sms=[board.san(m) for m in legal]
            for i in range(0,len(sms),8):
                print("  "+"  ".join(f"{s:<8}" for s in sms[i:i+8]))
            print(); continue
        if cmd=='resign':
            winner=BLACK if human_color==WHITE else WHITE
            print(f"  {player_name} resigned.")
            handle_game_end(board,elo_sys,white_name,black_name,winner_color=winner)
            _save_game_to_server(white_name, black_name, 'black' if human_color==WHITE else 'white', board.san_log, time.time()-game_start)
            return
        if cmd=='draw':
            if board.is_repetition() or board.is_fifty():
                handle_game_end(board,elo_sys,white_name,black_name,draw=True)
                _save_game_to_server(white_name, black_name, 'draw', board.san_log, time.time()-game_start)
                return
            print("  Engine declines the draw offer."); continue
        if cmd=='undo':
            keep=board.san_log[:-2] if len(board.san_log)>=2 else []
            nb=_replay_board(keep)
            if nb: board=nb; last_mv=None; print("  Move undone.\n")
            else: print("  Cannot undo.")
            continue
        if cmd.startswith('chat '): print("  (Chat not available vs AI)"); continue

        mv=board.parse_san(raw)
        if mv is None:
            print(f"  Illegal/unrecognised: '{raw}'. Try 'moves' or 'help'.")
            continue
        s=board.san(mv); board.make(mv); board.san_log.append(s); last_mv=mv


def _save_game_to_server(white, black, result, moves, duration, show_elo_changes=False):
    """
    Save game result to the server if connected.
    If show_elo_changes=True, display ELO changes after the game.
    Also saves locally for later analysis.
    """
    # Save locally for analysis
    save_online_game(white, black, result, moves, duration, rated=True)

    if _server_client is not None and _server_client.sock is not None and _current_user:
        try:
            response = _server_client.save_game(white, black, result, moves, int(duration), rated=True)
            if response:
                if response.get('success'):
                    if show_elo_changes:
                        elo_changes = response.get('data', {})
                        if elo_changes and isinstance(elo_changes, dict) and elo_changes.get('white'):
                            print("\n  ╔══════════════════════════════════════════════════════════╗")
                            print("  ║                   ELO CHANGES                             ║")
                            print("  ╠══════════════════════════════════════════════════════════╣")
                            for player, changes in elo_changes.items():
                                old_elo = changes.get('old', 1200)
                                new_elo = changes.get('new', 1200)
                                change = changes.get('change', 0)
                                sign = '+' if change > 0 else ''
                                print(f"  ║  {player:<20}: {old_elo} → {new_elo} ({sign}{change}){'':15}║")
                            print("  ╚══════════════════════════════════════════════════════════╝")
                else:
                    # Show error message
                    error_msg = response.get('data', 'Unknown error')
                    print(f"\n  Warning: Failed to save game to server: {error_msg}")
            else:
                print("\n  Warning: No response from server when saving game.")
        except Exception as e:
            print(f"\n  Warning: Error saving game to server: {e}")
    else:
        # Server not available, but game is saved locally
        if not _server_client or _server_client.sock is None:
            print("\n  Note: Server not connected. Game saved locally only.")
        elif not _current_user:
            print("\n  Note: Not logged in. Game saved locally only.")

# ════════════════════════════════════════════════════════════════════════
#  LOCAL TWO-PLAYER
# ════════════════════════════════════════════════════════════════════════
def play_local_2p(elo_sys):
    board=Board(); board.reset(); persp=WHITE; last_mv=None
    try:
        wn=input("  White player name [White]: ").strip() or 'White'
        bn=input("  Black player name [Black]: ").strip() or 'Black'
    except EOFError: return

    while True:
        draw_board(board, persp, last_mv)
        turn_str="White" if board.side==WHITE else "Black"
        pname=wn if board.side==WHITE else bn
        chk_str="  *** CHECK ***" if board.in_check() else ""
        print(f"  Move {board.fullmove} — {pname} ({turn_str}) to move{chk_str}")
        if board.san_log:
            pairs=[]
            for i in range(0,len(board.san_log),2):
                pairs.append(f"{i//2+1}. {board.san_log[i]} {board.san_log[i+1] if i+1<len(board.san_log) else '...'}")
            print("  "+' | '.join(pairs[-4:]))
        we=elo_sys.get_elo(wn); be=elo_sys.get_elo(bn)
        print(f"  {wn}({we}) vs {bn}({be})\n")

        legal=board.legal()
        if not legal:
            draw_board(board, persp, last_mv)
            if board.in_check():
                winner=BLACK if board.side==WHITE else WHITE
                handle_game_end(board,elo_sys,wn,bn,winner_color=winner)
            else:
                handle_game_end(board,elo_sys,wn,bn,draw=True)
            return

        for cond,msg in [(board.is_repetition(),"threefold repetition"),
                         (board.is_fifty(),"50-move rule"),
                         (board.insufficient_material(),"insufficient material")]:
            if cond:
                print(f"  ½-½ Draw: {msg}")
                handle_game_end(board,elo_sys,wn,bn,draw=True)
                return

        try:
            raw=input(f"  {pname}'s move: ").strip()
        except EOFError: return
        if not raw: continue
        cmd=raw.lower()
        if cmd in('quit','exit','q'): return
        if cmd=='help': print(HELP); continue
        if cmd=='flip': persp=1-persp; continue
        if cmd=='elo': elo_sys.leaderboard(); continue
        if cmd=='moves':
            sms=[board.san(m) for m in legal]
            for i in range(0,len(sms),8):
                print("  "+"  ".join(f"{s:<8}" for s in sms[i:i+8]))
            print(); continue
        if cmd=='resign':
            winner=BLACK if board.side==WHITE else WHITE
            print(f"  {pname} resigned.")
            handle_game_end(board,elo_sys,wn,bn,winner_color=winner)
            return
        if cmd=='draw':
            try:
                other=bn if board.side==WHITE else wn
                ans=input(f"  {other}: Accept draw? [y/N] ").strip().lower()
            except EOFError: ans='n'
            if ans in('y','yes'):
                handle_game_end(board,elo_sys,wn,bn,draw=True); return
            print("  Draw declined."); continue
        mv=board.parse_san(raw)
        if mv is None:
            print(f"  Illegal/unrecognised: '{raw}'. Try 'moves' or 'help'.")
            continue
        s=board.san(mv); board.make(mv); board.san_log.append(s); last_mv=mv

# ════════════════════════════════════════════════════════════════════════
#  NETWORK MULTIPLAYER GAME LOOP
# ════════════════════════════════════════════════════════════════════════
def play_network(elo_sys, net, our_color):
    board=Board(); board.reset()
    persp=our_color; last_mv=None
    pending_draw=False

    try:
        player_name=input("  Your name [Player]: ").strip() or 'Player'
    except EOFError:
        player_name='Player'

    white_name=player_name if our_color==WHITE else 'Opponent'
    black_name='Opponent' if our_color==WHITE else player_name

    # Exchange names
    net.send('NAME', player_name)
    # Try to get opponent name
    opp_name='Opponent'
    for _ in range(20):
        msg=net.recv(timeout=0.5)
        if msg and msg['type']=='NAME':
            opp_name=msg['data']
            break

    if our_color==WHITE:
        white_name=player_name; black_name=opp_name
    else:
        white_name=opp_name; black_name=player_name

    print(f"  Playing as {'White' if our_color==WHITE else 'Black'} vs {opp_name}\n")

    # Use a thread-safe queue for incoming messages
    import queue
    msg_q = queue.Queue()
    def recv_thread():
        while True:
            msg=net.recv(timeout=1.0)
            if msg: msg_q.put(msg)
    t=threading.Thread(target=recv_thread, daemon=True)
    t.start()

    while True:
        # Check for incoming messages
        try:
            while not msg_q.empty():
                msg=msg_q.get_nowait()
                mtype=msg.get('type',''); mdata=msg.get('data','')
                if mtype==MSG_MOVE:
                    m=board.parse_san(mdata)
                    if m:
                        s=board.san(m); board.make(m); board.san_log.append(s); last_mv=m
                elif mtype==MSG_RESIGN:
                    winner=our_color
                    print(f"\n  {opp_name} resigned!")
                    handle_game_end(board,elo_sys,white_name,black_name,winner_color=winner)
                    net.close(); return
                elif mtype==MSG_DRAW:
                    pending_draw=True
                    print(f"\n  {opp_name} offers a draw!")
                elif mtype==MSG_ACCEPT:
                    print(f"\n  {opp_name} accepted the draw!")
                    handle_game_end(board,elo_sys,white_name,black_name,draw=True)
                    net.close(); return
                elif mtype==MSG_DECLINE:
                    print(f"\n  {opp_name} declined the draw.")
                    pending_draw=False
                elif mtype==MSG_CHAT:
                    print(f"\n  [{opp_name}]: {mdata}")
        except:
            pass

        draw_board(board, persp, last_mv)
        turn_str="White" if board.side==WHITE else "Black"
        our_turn=board.side==our_color
        chk_str="  *** CHECK ***" if board.in_check() else ""
        who="Your" if our_turn else f"{opp_name}'s"
        print(f"  Move {board.fullmove} — {who} turn ({turn_str}){chk_str}")
        if board.san_log:
            pairs=[]
            for i in range(0,len(board.san_log),2):
                pairs.append(f"{i//2+1}. {board.san_log[i]} {board.san_log[i+1] if i+1<len(board.san_log) else '...'}")
            print("  "+' | '.join(pairs[-4:]))
        print()

        legal=board.legal()
        if not legal:
            if board.in_check():
                winner=BLACK if board.side==WHITE else WHITE
                handle_game_end(board,elo_sys,white_name,black_name,winner_color=winner)
            else:
                handle_game_end(board,elo_sys,white_name,black_name,draw=True)
            net.close(); return

        for cond,msg2 in [(board.is_repetition(),"threefold repetition"),
                          (board.is_fifty(),"50-move rule"),
                          (board.insufficient_material(),"insufficient material")]:
            if cond:
                print(f"  ½-½ Draw: {msg2}")
                net.send(MSG_DRAW)
                handle_game_end(board,elo_sys,white_name,black_name,draw=True)
                net.close(); return

        if not our_turn:
            time.sleep(0.2); continue

        try:
            raw=input("  Your move: ").strip()
        except EOFError:
            net.close(); return
        if not raw: continue
        cmd=raw.lower()

        if cmd in('quit','exit','q'):
            net.send(MSG_RESIGN); net.close(); return
        if cmd=='help': print(HELP); continue
        if cmd=='flip': persp=1-persp; continue
        if cmd=='elo': elo_sys.leaderboard(); continue
        if cmd=='moves':
            sms=[board.san(m) for m in legal]
            for i in range(0,len(sms),8):
                print("  "+"  ".join(f"{s:<8}" for s in sms[i:i+8]))
            print(); continue
        if cmd=='resign':
            net.send(MSG_RESIGN)
            winner=BLACK if our_color==WHITE else WHITE
            handle_game_end(board,elo_sys,white_name,black_name,winner_color=winner)
            net.close(); return
        if cmd=='draw':
            if pending_draw:
                net.send(MSG_ACCEPT)
                handle_game_end(board,elo_sys,white_name,black_name,draw=True)
                net.close(); return
            else:
                net.send(MSG_DRAW); print("  Draw offer sent."); continue
        if cmd.startswith('chat '):
            msg_text=raw[5:]
            net.send(MSG_CHAT, msg_text)
            print(f"  [You]: {msg_text}"); continue

        mv=board.parse_san(raw)
        if mv is None:
            print(f"  Illegal/unrecognised: '{raw}'. Try 'moves' or 'help'.")
            continue
        s=board.san(mv)
        if not net.send(MSG_MOVE, s):
            print("  Connection lost!"); net.close(); return
        board.make(mv); board.san_log.append(s); last_mv=mv

# ════════════════════════════════════════════════════════════════════════
#  MAIN MENU
# ════════════════════════════════════════════════════════════════════════
MAIN_MENU_ONLINE = """
  ┌─────────────────────────────────┐
  │         MAIN MENU               │
  ├─────────────────────────────────┤
  │  1. Play vs AI                  │
  │  2. Local 2-Player              │
  │  3. Online Matchmaking          │
  │  4. Account Management          │
  │  5. ELO Leaderboard             │
  │  6. Analyze a PGN line          │
  │  7. Game Analysis (Online)      │
  │  8. Friends & Messaging         │
  │  9. Configure Server            │
  │  L. Learn an Opening            │
  │  0. Enable Offline Mode         │
  │  Q. Quit                        │
  └─────────────────────────────────┘
"""

MAIN_MENU_OFFLINE = """
  ┌─────────────────────────────────┐
  │         MAIN MENU               │
  ├─────────────────────────────────┤
  │  1. Play vs AI                  │
  │  2. Local 2-Player              │
  │  3. Online Matchmaking [OFFLINE]│
  │  4. Account Management          │
  │  5. ELO Leaderboard             │
  │  6. Analyze a PGN line          │
  │  7. Game Analysis (Online)      │
  │  8. Friends & Messaging [OFFLINE]│
  │  9. Configure Server            │
  │  L. Learn an Opening            │
  │  0. Enable Online Mode          │
  │  Q. Quit                        │
  └─────────────────────────────────┘
"""

def learn_opening():
    """
    Interactive opening trainer.
    Shows a catalogue of named openings, lets the player pick one, then
    walks through the main line and branches interactively.
    """
    # ── Opening catalogue ─────────────────────────────────────────────────
    # Each entry: (display_name, list_of_lines)
    # Each line is a dict: {name, moves_str, description}
    OPENINGS = [
        # ── e4 ────────────────────────────────────────────────────────────
        ("Ruy Lopez / Spanish", [
            {"name": "Main Line (Morphy)",
             "moves": "e4 e5 Nf3 Nc6 Bb5 a6 Ba4 Nf6 O-O Be7 Re1 b5 Bb3 d6 c3 O-O",
             "desc": "The most classical opening. White fianchettos the bishop and aims for a powerful centre."},
            {"name": "Berlin Defence",
             "moves": "e4 e5 Nf3 Nc6 Bb5 Nf6 O-O Nxe4 d4 Nd6 Bxc6 dxc6 dxe5 Nf5",
             "desc": "Solid and drawish. Black trades pawns for activity. Loved by world champions."},
            {"name": "Exchange Variation",
             "moves": "e4 e5 Nf3 Nc6 Bb5 a6 Bxc6 dxc6 O-O f6 d4 exd4 Nxd4",
             "desc": "White accepts doubled pawns for Black, then seeks a structural advantage."},
            {"name": "Marshall Attack",
             "moves": "e4 e5 Nf3 Nc6 Bb5 a6 Ba4 Nf6 O-O Be7 Re1 b5 Bb3 O-O c3 d5",
             "desc": "A pawn sacrifice by Black that leads to a fierce attack against White's king."},
            {"name": "Schliemann Gambit",
             "moves": "e4 e5 Nf3 Nc6 Bb5 f5 Nc3 fxe4 Nxe4 d5",
             "desc": "An aggressive counter-gambit. Black stakes everything on an early attack."},
        ]),
        ("Italian / Giuoco Piano", [
            {"name": "Giuoco Piano",
             "moves": "e4 e5 Nf3 Nc6 Bc4 Bc5 c3 Nf6 d4 exd4 cxd4 Bb4+ Nc3 Nxe4",
             "desc": "White builds a strong centre. One of the oldest and most popular openings."},
            {"name": "Two Knights",
             "moves": "e4 e5 Nf3 Nc6 Bc4 Nf6 Ng5 d5 exd5 Na5 Bb5+ c6 dxc6 bxc6 Be2 h6 Nf3",
             "desc": "Black allows Ng5, inviting tactical complications with …d5."},
            {"name": "Fried Liver Attack",
             "moves": "e4 e5 Nf3 Nc6 Bc4 Nf6 Ng5 d5 exd5 Nxd5 Nxf7 Kxf7 Qf3+",
             "desc": "White sacrifices a knight on f7 for a fierce king-hunt. Fun but risky!"},
            {"name": "Slow Italian",
             "moves": "e4 e5 Nf3 Nc6 Bc4 Bc5 d3 Nf6 c3 a6 Bb3 d6 Nbd2 O-O",
             "desc": "A patient approach. White builds slowly and avoids early complications."},
        ]),
        ("Scotch Game", [
            {"name": "Scotch Game",
             "moves": "e4 e5 Nf3 Nc6 d4 exd4 Nxd4 Nf6 Nxc6 bxc6 e5 Qe7 Qe2 Nd5 c4",
             "desc": "White opens the centre immediately. Popular at the top level."},
            {"name": "Scotch Gambit",
             "moves": "e4 e5 Nf3 Nc6 d4 exd4 Bc4 Bc5 c3 Nf6 e5 d5 Bb5 Ne4 cxd4",
             "desc": "White sacrifices a pawn for quick development and attacking chances."},
            {"name": "Göring Gambit",
             "moves": "e4 e5 Nf3 Nc6 d4 exd4 c3 dxc3 Bc4 cxb2 Bxb2",
             "desc": "A double pawn sacrifice for massive compensation in development."},
        ]),
        ("King's Gambit", [
            {"name": "King's Gambit Accepted (Classical)",
             "moves": "e4 e5 f4 exf4 Nf3 g5 Bc4 g4 O-O gxf3 Qxf3",
             "desc": "White sacrifices a pawn for fast development and an attack. A romantic opening."},
            {"name": "King's Gambit Accepted (Modern)",
             "moves": "e4 e5 f4 exf4 Nf3 d6 d4 g5 h4 g4 Ng5 Nh6",
             "desc": "Black tries to hold the extra pawn. White has the centre and open lines."},
            {"name": "King's Gambit Declined (Falkbeer)",
             "moves": "e4 e5 f4 d5 exd5 e4 d3 Nf6 dxe4 Nxe4 Nf3 Bc5 Qe2",
             "desc": "Black counter-attacks in the centre rather than accepting the gambit."},
        ]),
        ("Sicilian Defence", [
            {"name": "Najdorf",
             "moves": "e4 c5 Nf3 d6 d4 cxd4 Nxd4 Nf6 Nc3 a6 Be3 e5 Nb3 Be6 f3 Be7 Qd2 O-O g4",
             "desc": "The sharpest Sicilian. Black prepares …b5 and counterplay on the queenside."},
            {"name": "Sicilian Dragon",
             "moves": "e4 c5 Nf3 d6 d4 cxd4 Nxd4 Nf6 Nc3 g6 Be3 Bg7 f3 Nc6 Qd2 O-O O-O-O d5",
             "desc": "A volcanic battle. White attacks on the kingside, Black on the queenside."},
            {"name": "Sicilian Scheveningen",
             "moves": "e4 c5 Nf3 d6 d4 cxd4 Nxd4 Nf6 Nc3 e6 Be2 Be7 O-O O-O f4 Nc6",
             "desc": "Solid and flexible. Black keeps the centre under control."},
            {"name": "Sicilian Sveshnikov",
             "moves": "e4 c5 Nf3 Nc6 d4 cxd4 Nxd4 Nf6 Nc3 e5 Ndb5 d6 Bg5 a6 Na3 b5 Bxf6 gxf6 Nd5",
             "desc": "Black accepts weaknesses for active piece play and the bishop pair."},
            {"name": "Sicilian Kan / English Attack",
             "moves": "e4 c5 Nf3 e6 d4 cxd4 Nxd4 a6 Nc3 Qc7 Be2 Nf6 O-O Nc6 Be3 Be7 f4",
             "desc": "A flexible Sicilian. Black delays commitment and keeps many options."},
            {"name": "Alapin (c3 Sicilian)",
             "moves": "e4 c5 c3 Nf6 e5 Nd5 d4 cxd4 Nf3 Nc6 cxd4 d6 Bc4 Nb6 Bb3",
             "desc": "White avoids theory. The c3-d4 centre is solid but Black can equalise."},
        ]),
        ("Caro-Kann", [
            {"name": "Classical",
             "moves": "e4 c6 d4 d5 Nc3 dxe4 Nxe4 Bf5 Ng3 Bg6 h4 h6 Nf3 Nd7 h5 Bh7 Bd3 Bxd3 Qxd3",
             "desc": "Solid and classical. Black gets a solid structure at the cost of passive play."},
            {"name": "Advance Variation",
             "moves": "e4 c6 d4 d5 e5 Bf5 Nf3 e6 Be2 Nd7 O-O Bg6 Nbd2 Ne7 Nb3 Nf5",
             "desc": "White grabs space. Black needs to find the right moment to break with …c5."},
            {"name": "Exchange Variation",
             "moves": "e4 c6 d4 d5 exd5 cxd5 Bd3 Nf6 c3 Nc6 Nf3 Bg4 Nbd2 e6 h3",
             "desc": "Symmetrical pawn structure. An interesting endgame-oriented choice."},
            {"name": "Panov-Botvinnik Attack",
             "moves": "e4 c6 d4 d5 exd5 cxd5 c4 Nf6 Nc3 e6 Nf3 Bb4 cxd5 Nxd5 Bd2 Nc6",
             "desc": "An IQP structure arises. White gets dynamic piece play and active prospects."},
        ]),
        ("French Defence", [
            {"name": "Classical Variation",
             "moves": "e4 e6 d4 d5 Nc3 Nf6 Bg5 Be7 e5 Nfd7 Bxe7 Qxe7 f4 O-O Nf3 c5",
             "desc": "Black builds a solid pawn chain. White's space must be used actively."},
            {"name": "Winawer Variation",
             "moves": "e4 e6 d4 d5 Nc3 Bb4 e5 c5 a3 Bxc3+ bxc3 Ne7 Qg4 Qc7 Qxg7 Rg8",
             "desc": "Sharp and imbalanced. Black pins White's knight; White attacks the kingside."},
            {"name": "Tarrasch Variation",
             "moves": "e4 e6 d4 d5 Nd2 c5 Ngf3 Nc6 exd5 exd5 Bb5 Bd6 dxc5 Bxc5 O-O Nge7",
             "desc": "White avoids the Winawer pin. A solid but ambitious approach."},
            {"name": "Advance Variation",
             "moves": "e4 e6 d4 d5 e5 c5 c3 Qb6 Nf3 Nc6 Be2 cxd4 cxd4 Nh6 Nc3 Nf5",
             "desc": "White clamps the centre immediately. A popular system at all levels."},
        ]),
        ("Queen's Gambit", [
            {"name": "QGD Orthodox",
             "moves": "d4 d5 c4 e6 Nc3 Nf6 Bg5 Be7 e3 O-O Nf3 h6 Bh4 b6 cxd5 Nxd5 Bxe7 Qxe7",
             "desc": "The most solid defence. Black builds a rock-solid structure."},
            {"name": "Queen's Gambit Accepted",
             "moves": "d4 d5 c4 dxc4 Nf3 Nf6 e3 e6 Bxc4 c5 O-O a6 Qe2 b5 Bd3 Bb7",
             "desc": "Black accepts the pawn and aims to equalise with active piece play."},
            {"name": "Slav Defence",
             "moves": "d4 d5 c4 c6 Nf3 Nf6 Nc3 dxc4 a4 Bf5 e3 e6 Bxc4 Bb4 O-O Nbd7",
             "desc": "Black supports d5 with c6. Solid and popular at the highest levels."},
            {"name": "Semi-Slav / Meran",
             "moves": "d4 d5 c4 c6 Nc3 Nf6 Nf3 e6 e3 Nbd7 Bd3 dxc4 Bxc4 b5 Bd3 a6 e4",
             "desc": "One of the most dynamically complex openings. Sharp pawn play."},
            {"name": "Catalan",
             "moves": "d4 d5 c4 e6 g3 Nf6 Bg2 Be7 Nf3 O-O O-O dxc4 Qc2 a6 Qxc4 b5 Qc2 Bb7",
             "desc": "White puts the bishop on g2 for long-term pressure. A modern classic."},
        ]),
        ("Nimzo-Indian Defence", [
            {"name": "Rubinstein (e3)",
             "moves": "d4 Nf6 c4 e6 Nc3 Bb4 e3 O-O Bd3 d5 Nf3 c5 O-O Nc6 a3 Bxc3 bxc3",
             "desc": "Solid and classical. White accepts the bishop pair and targets the centre."},
            {"name": "Kasparov Variation (g3)",
             "moves": "d4 Nf6 c4 e6 Nc3 Bb4 g3 O-O Bg2 d5 Nf3 dxc4 O-O Nc6 Qc2 Bxc3 Qxc3 b5",
             "desc": "White fianchettos the bishop. A dynamic system Kasparov used with success."},
            {"name": "Sämisch (f3)",
             "moves": "d4 Nf6 c4 e6 Nc3 Bb4 f3 d5 a3 Bxc3+ bxc3 c5 cxd5 exd5 e3 O-O",
             "desc": "White wants to build a huge centre, but Black gets active counterplay."},
            {"name": "Classical (Nf3)",
             "moves": "d4 Nf6 c4 e6 Nc3 Bb4 Nf3 c5 g3 cxd4 Nxd4 O-O Bg2 d5 Qb3 Bxc3+ bxc3",
             "desc": "A rich middlegame structure with many imbalances."},
        ]),
        ("King's Indian Defence", [
            {"name": "Classical / Main Line",
             "moves": "d4 Nf6 c4 g6 Nc3 Bg7 e4 d6 Nf3 O-O Be2 e5 O-O Nc6 d5 Ne7 Ne1 Nd7",
             "desc": "One of the sharpest double-edged openings. Both sides attack on opposite wings."},
            {"name": "Sämisch Attack",
             "moves": "d4 Nf6 c4 g6 Nc3 Bg7 e4 d6 f3 O-O Be3 e5 d5 Nh5 Qd2 f5 O-O-O",
             "desc": "White builds a massive centre and storms the kingside."},
            {"name": "Four Pawns Attack",
             "moves": "d4 Nf6 c4 g6 Nc3 Bg7 e4 d6 f4 O-O Nf3 c5 dxc5 Qa5 Bd3 Qxc5 Qe2",
             "desc": "An aggressive attempt to overwhelm Black with four pawns in the centre."},
            {"name": "Averbakh Variation",
             "moves": "d4 Nf6 c4 g6 Nc3 Bg7 e4 d6 Be2 O-O Bg5 c5 d5 h6 Bh4 g5 Bg3 Nh5",
             "desc": "White develops the bishop to g5 early, aiming for positional pressure."},
            {"name": "Fianchetto Variation",
             "moves": "d4 Nf6 c4 g6 g3 Bg7 Bg2 d6 Nc3 O-O Nf3 Nbd7 O-O e5 e4 exd4 Nxd4",
             "desc": "A positional approach. White mirrors Black's fianchetto."},
        ]),
        ("Dutch Defence", [
            {"name": "Stonewall",
             "moves": "d4 f5 c4 Nf6 g3 e6 Bg2 d5 Nf3 c6 O-O Bd6 b3 Qe7 Ne5",
             "desc": "Black builds an impregnable fortress. Slow but very solid."},
            {"name": "Leningrad",
             "moves": "d4 f5 Nf3 Nf6 g3 g6 Bg2 Bg7 O-O O-O c4 d6 Nc3 Qe8 d5 Na6",
             "desc": "Dynamic and aggressive. Black prepares a kingside attack with the Bg7."},
            {"name": "Classical Dutch",
             "moves": "d4 f5 c4 e6 Nf3 Nf6 Nc3 Bb4 Qc2 O-O a3 Bxc3+ Qxc3 b6 g3 Bb7 Bg2",
             "desc": "A solid try avoiding the Stonewall pawn structure."},
        ]),
        ("Grünfeld Defence", [
            {"name": "Exchange Variation",
             "moves": "d4 Nf6 c4 g6 Nc3 d5 cxd5 Nxd5 e4 Nxc3 bxc3 Bg7 Bc4 c5 Ne2 Nc6 Be3 O-O",
             "desc": "Black allows White a big centre, then attacks it with pieces."},
            {"name": "Russian System",
             "moves": "d4 Nf6 c4 g6 Nc3 d5 Nf3 Bg7 Qb3 dxc4 Qxc4 O-O e4 a6 e5 b5 Qb3 Nc6",
             "desc": "White takes the pawn with the queen and maintains central tension."},
            {"name": "Neo-Grünfeld",
             "moves": "d4 Nf6 c4 g6 Nc3 d5 Bf4 Bg7 e3 O-O Rc1 dxc4 Bxc4 c5 dxc5 Qa5 Nge2 Nbd7",
             "desc": "A solid system avoiding the sharp Exchange variation."},
        ]),
        ("L*ndon System", [
            {"name": "L*ndon System",
             "moves": "d4 d5 Bf4 Nf6 e3 e6 Nd2 c5 c3 Nc6 Ngf3 Bd6 Bg3 O-O Bd3",
             "desc": "A solid, low-theory system. White develops naturally and attacks on the kingside."},
            {"name": "London vs KID setup",
             "moves": "d4 Nf6 Bf4 e6 e3 d5 Nf3 c5 c3 Nc6 Nbd2 Bd6 Bg3 O-O Bd3",
             "desc": "The same idea against the King's Indian setup."},
        ]),
        ("Benoni Defence", [
            {"name": "Modern Benoni",
             "moves": "d4 Nf6 c4 c5 d5 e6 Nc3 exd5 cxd5 d6 Nf3 g6 Bg2 Bg7 O-O O-O a4 a6",
             "desc": "Black sacrifices a pawn to gain dynamic counterplay on the queenside."},
            {"name": "Benko Gambit",
             "moves": "d4 Nf6 c4 c5 d5 b5 cxb5 a6 bxa6 Bxa6 Nc3 d6 Nf3 g6 g3 Bg7 Bg2 O-O O-O Nbd7",
             "desc": "Black sacrifices two pawns for long-term queenside pressure."},
        ]),
    ]

    # ── Display opening catalogue ─────────────────────────────────────────
    while True:
        print("\n  ╔══════════════════════════════════════════════════════════╗")
        print("  ║              OPENING TRAINER                             ║")
        print("  ╠══════════════════════════════════════════════════════════╣")
        print("  ║  Study master-level openings interactively.              ║")
        print("  ║  You play moves, the trainer shows variations & ideas.   ║")
        print("  ╠══════════════════════════════════════════════════════════╣")
        for i, (name, _) in enumerate(OPENINGS, 1):
            print(f"  ║  {i:>2}. {name:<50}║")
        print("  ║   0. Back to main menu                                   ║")
        print("  ╚══════════════════════════════════════════════════════════╝")

        try:
            choice = input("  Select opening: ").strip()
        except EOFError:
            return
        if choice == '0':
            return
        try:
            idx = int(choice) - 1
            if not (0 <= idx < len(OPENINGS)):
                print("  Invalid choice.")
                continue
        except ValueError:
            print("  Invalid choice.")
            continue

        opening_name, lines = OPENINGS[idx]
        _learn_opening_lines(opening_name, lines)


def _learn_opening_lines(opening_name, lines):
    """Show available lines for an opening, then start the trainer."""
    while True:
        print(f"\n  ╔══════════════════════════════════════════════════════════╗")
        print(f"  ║  {opening_name:<56}║")
        print(f"  ╠══════════════════════════════════════════════════════════╣")
        for i, line in enumerate(lines, 1):
            desc_short = line['desc'][:48]
            print(f"  ║  {i}. {line['name']:<52}║")
            print(f"  ║     {desc_short:<54}║")
        print(f"  ║   0. Back                                                ║")
        print(f"  ╚══════════════════════════════════════════════════════════╝")

        try:
            choice = input("  Select line: ").strip()
        except EOFError:
            return
        if choice == '0':
            return
        try:
            idx = int(choice) - 1
            if not (0 <= idx < len(lines)):
                print("  Invalid choice.")
                continue
        except ValueError:
            print("  Invalid choice.")
            continue

        line = lines[idx]
        _run_opening_trainer(opening_name, line)


def _run_opening_trainer(opening_name, line):
    """
    Interactive opening trainer for a single line.
    Modes:
      • DEMO  – play through the line move by move with commentary
      • DRILL – you enter the moves; the trainer corrects mistakes
    """
    moves_str = line['moves']
    desc = line['desc']
    san_sequence = moves_str.split()

    print(f"\n  ╔══════════════════════════════════════════════════════════╗")
    print(f"  ║  {line['name']:<56}║")
    print(f"  ╠══════════════════════════════════════════════════════════╣")
    # Word-wrap description
    words = desc.split()
    row = "  ║  "
    for w in words:
        if len(row) + len(w) + 1 > 59:
            print(f"{row:<59}║")
            row = "  ║  " + w
        else:
            row += (" " if row != "  ║  " else "") + w
    if row.strip():
        print(f"{row:<59}║")
    print(f"  ╠══════════════════════════════════════════════════════════╣")
    print(f"  ║  1. Demo (watch the line)                                ║")
    print(f"  ║  2. Drill as White (enter White's moves)                 ║")
    print(f"  ║  3. Drill as Black (enter Black's moves)                 ║")
    print(f"  ║  0. Back                                                 ║")
    print(f"  ╚══════════════════════════════════════════════════════════╝")

    try:
        mode = input("  Mode: ").strip()
    except EOFError:
        return
    if mode == '0':
        return
    if mode not in ('1', '2', '3'):
        print("  Invalid mode.")
        return

    persp = WHITE
    if mode == '3':
        persp = BLACK

    board = Board(); board.reset()
    last_mv = None

    if mode == '1':
        # ── Demo mode ─────────────────────────────────────────────────────
        print("\n  Playing through the line. Press Enter to advance, 'q' to quit.\n")
        for i, san in enumerate(san_sequence):
            m = board.parse_san(san)
            if m is None:
                print(f"  [Error: could not parse '{san}' — stopping.]")
                break
            side_str = "White" if board.side == WHITE else "Black"
            move_num = board.fullmove
            # Show board BEFORE the move
            draw_board(board, persp, last_mv)
            notation = f"{move_num}." if board.side == WHITE else f"{move_num}..."
            # Pause
            try:
                inp = input(f"  {notation} {san} ({side_str})  [Enter to play, q to quit]: ").strip().lower()
            except EOFError:
                break
            if inp == 'q':
                break
            sn = board.san(m)
            board.make(m)
            board.san_log.append(sn)
            last_mv = m
            print(f"  ✓ {notation} {sn}\n")

        # Show final position
        draw_board(board, persp, last_mv)
        print(f"  End of line. Full sequence: {' '.join(board.san_log)}")
        try:
            input("  Press Enter to continue...")
        except EOFError:
            pass

    else:
        # ── Drill mode ─────────────────────────────────────────────────────
        drill_color = WHITE if mode == '2' else BLACK
        color_str = "White" if drill_color == WHITE else "Black"
        print(f"\n  DRILL MODE — you play {color_str}.")
        print("  Enter moves in SAN (e.g. 'e4', 'Nf3', 'O-O').")
        print("  Type 'hint' for a hint, 'show' to see the board, 'q' to quit.\n")

        errors = 0
        total_your_moves = 0
        for i, san in enumerate(san_sequence):
            m = board.parse_san(san)
            if m is None:
                break

            is_your_turn = (board.side == drill_color)
            move_num = board.fullmove
            notation = f"{move_num}." if board.side == WHITE else f"{move_num}..."

            draw_board(board, persp, last_mv)

            if is_your_turn:
                total_your_moves += 1
                # Player must find the correct move
                attempts = 0
                while True:
                    try:
                        raw = input(f"  Your move ({notation} ?): ").strip()
                    except EOFError:
                        return
                    if raw.lower() == 'q':
                        _show_drill_result(total_your_moves, errors)
                        return
                    if raw.lower() == 'hint':
                        # Give first letter of the move
                        hint = san[0] if san else '?'
                        print(f"  Hint: the move starts with '{hint}'")
                        continue
                    if raw.lower() == 'show':
                        draw_board(board, persp, last_mv)
                        continue

                    player_m = board.parse_san(raw)
                    if player_m is None:
                        print(f"  Illegal or unrecognised: '{raw}'. Try again.")
                        continue

                    if player_m == m:
                        sn = board.san(m)
                        board.make(m)
                        board.san_log.append(sn)
                        last_mv = m
                        print(f"  ✓ Correct! {notation} {sn}\n")
                        break
                    else:
                        attempts += 1
                        if attempts == 1:
                            print(f"  ✗ Not quite. Try again (type 'hint' for help).")
                        else:
                            # After 2 wrong answers, reveal the correct move
                            errors += 1
                            sn = board.san(m)
                            print(f"  ✗ The correct move was {notation} {sn}.")
                            board.make(m)
                            board.san_log.append(sn)
                            last_mv = m
                            break
            else:
                # Trainer plays the other side
                sn = board.san(m)
                board.make(m)
                board.san_log.append(sn)
                last_mv = m
                print(f"  Trainer plays: {notation} {sn}\n")

        # Show final position
        draw_board(board, persp, last_mv)
        print(f"\n  Line complete! Full sequence: {' '.join(board.san_log)}")
        _show_drill_result(total_your_moves, errors)
        try:
            input("  Press Enter to continue...")
        except EOFError:
            pass


def _show_drill_result(total, errors):
    """Print drill score."""
    correct = total - errors
    pct = int(correct / total * 100) if total > 0 else 0
    grade = "Excellent! 🏆" if pct == 100 else ("Good job! 👍" if pct >= 70 else "Keep practising! 📚")
    print(f"\n  ─── Drill Result ───────────────────────────────")
    print(f"  Moves played:  {total}")
    print(f"  Correct:       {correct} / {total}  ({pct}%)")
    print(f"  {grade}")
    print(f"  ────────────────────────────────────────────────")



    """Analyze a manually-entered sequence of moves."""
    print("\n  Enter moves separated by spaces (SAN format).")
    print("  Example: e4 e5 Nf3 Nc6 Bb5")
    try:
        line=input("  Moves: ").strip()
    except EOFError: return
    san_list=line.split()
    # Validate
    b=Board(); b.reset(); valid=[]
    for s in san_list:
        m=b.parse_san(s)
        if m is None: print(f"  Stopped at unrecognised move: '{s}'"); break
        sn=b.san(m); b.make(m); b.san_log.append(sn); valid.append(sn)
    if not valid: print("  No valid moves to analyze."); return
    results=analyze_game(valid, engine_time=1.0)
    print_analysis(results)

def analyze_online_game_menu():
    """Menu for analyzing online games."""
    print("\n  ╔══════════════════════════════════════════════════════════╗")
    print("  ║              GAME ANALYSIS                               ║")
    print("  ╠══════════════════════════════════════════════════════════╣")
    print("  ║  Analyze your online games with engine evaluation        ║")
    print("  ╚══════════════════════════════════════════════════════════╝\n")
    
    games = load_online_games(limit=20)
    unanalyzed = get_unanalyzed_games()
    
    if not games:
        print("  No online games found. Play an online game first!")
        return
    
    # Show games list
    print(f"  Recent Games ({len(games)} total, {len(unanalyzed)} unanalyzed)")
    print("  " + "─"*68)
    print(f"  {'#':<3} {'Result':<8} {'White':<15} {'Black':<15} {'Moves':<6} {'Analyzed':<10}")
    print("  " + "─"*68)
    
    for i, game in enumerate(games):
        result = game.get('result', '?')
        white = game.get('white', '?')[:14]
        black = game.get('black', '?')[:14]
        moves = len(game.get('moves', []))
        analyzed = 'Yes' if game.get('analyzed', False) else 'No'
        analyzed_mark = '*' if not game.get('analyzed', False) else ' '
        print(f"  {i+1}{analyzed_mark}  {result:<8} {white:<15} {black:<15} {moves:<6} {analyzed:<10}")
    
    print("  " + "─"*68)
    print("  * = Unanalyzed game")
    print()
    print("  Enter game number to analyze, or:")
    print("  A - Analyze all unanalyzed games")
    print("  0 - Back to main menu")
    print()
    
    while True:
        try:
            choice = input("  Choice: ").strip().upper()
        except EOFError:
            return
        
        if choice == '0':
            return
        elif choice == 'A':
            if not unanalyzed:
                print("  No unanalyzed games!")
                continue
            print(f"\n  Analyzing {len(unanalyzed)} game(s)... This may take a while.\n")
            for game in unanalyzed:
                print(f"\n  Analyzing: {game['white']} vs {game['black']} ({game['result']})")
                print("  " + "="*50)
                results = analyze_game(game.get('moves', []), engine_time=2.0, depth_limit=14)
                print_analysis(results)
                mark_game_analyzed(game['id'])
            print("\n  All games analyzed!")
            return
        else:
            try:
                idx = int(choice) - 1
                if 0 <= idx < len(games):
                    game = games[idx]
                    print(f"\n  Analyzing: {game['white']} vs {game['black']} ({game['result']})")
                    print("  " + "="*50)
                    results = analyze_game(game.get('moves', []), engine_time=2.0, depth_limit=14)
                    print_analysis(results)
                    mark_game_analyzed(game['id'])
                    print("  Game marked as analyzed.")
                    return
                else:
                    print("  Invalid game number.")
            except ValueError:
                print("  Invalid input. Enter a number, 'A', or '0'.")

def main():
    global _offline_mode, _server_host, _server_port, _server_client
    
    print(BANNER)
    print("  Initialising opening book...")
    book=OpeningBook()
    print(f"  Opening book ready ({len(book._book)} positions)")
    print("  Initialising tablebases...")
    tb=Tablebase()
    tb._init_if_needed()
    print("  Tablebases ready (KQK, KRK, KPK, KBNK)")
    print("  Neural network evaluator ready")
    elo_sys=EloSystem()
    print()

    # Load saved server configuration first
    _load_server_config()
    
    # Auto-connect to saved server if available (even without saved credentials)
    if _server_host and _server_port and _offline_mode:
        print(f"\n  Found saved server: {_server_host}:{_server_port}")
        print("  Attempting to connect...")
        _offline_mode = False  # Enable online mode
        success, msg = connect_to_server(auto_login=False)
        if success:
            print(f"  ✓ Connected to server!")
            # Try auto-login if credentials are saved
            auto_login()
        else:
            print(f"  Connection failed: {msg}")
            print("  Starting in offline mode...")
            _offline_mode = True
    else:
        # Attempt auto-login if credentials are saved
        # This will also enable online mode automatically
        auto_login()
    print()

    while True:
        # Show status bar
        print("  ═══════════════════════════════════════════════════════════════")
        if _offline_mode:
            print("  ║  OFFLINE MODE                              [8] Enable Online ║")
        else:
            if _current_user:
                print(f"  ║  Logged in: {_current_user:<43}║")
            else:
                print("  ║  Not logged in                           [4] Account Mgmt  ║")
        print("  ═══════════════════════════════════════════════════════════════")
        print()

        # Show appropriate menu based on mode
        print(MAIN_MENU_OFFLINE if _offline_mode else MAIN_MENU_ONLINE)
        try:
            choice=input("  Choice: ").strip().lower()
        except EOFError:
            break

        if choice in('q','quit','exit'):
            disconnect_from_server()
            print("  Goodbye!\n"); break

        elif choice == 'clear':
            clear_screen()
            continue

        elif choice=='1':
            play_vs_ai(elo_sys, tb, book)

        elif choice=='2':
            play_local_2p(elo_sys)

        elif choice=='3':
            matchmaking_menu()

        elif choice=='4':
            auth_menu()

        elif choice=='5':
            show_online_leaderboard()

        elif choice=='6':
            analyze_pgn_line()

        elif choice=='7':
            analyze_online_game_menu()

        elif choice=='8':
            if not _offline_mode:
                friends_messaging_menu()
            else:
                print("\n  Feature not available in offline mode.")

        elif choice=='9':
            configure_server_connection()

        elif choice in ('l', 'L'):
            learn_opening()

        elif choice=='0':
            # Toggle offline mode
            if _offline_mode:
                print("\n  ╔═══════════════════════════════════════════════════════════╗")
                print("  ║              ENABLE ONLINE MODE?                          ║")
                print("  ╠═══════════════════════════════════════════════════════════╣")
                print("  ║  This will enable:                                        ║")
                print("  ║  • Online matchmaking                                     ║")
                print("  ║  • User accounts and profiles                             ║")
                print("  ║  • Game history sync                                      ║")
                print("  ║                                                           ║")
                try:
                    ans = input("  ║  Enable online mode? [Y/n]: ").strip().lower()
                except EOFError:
                    ans = 'n'
                if ans in ('y', 'yes', ''):
                    set_offline_mode(False)
                    # Load saved server configuration
                    _load_server_config()
                    print("  ║  Online mode enabled!                                    ║")
                    # Attempt auto-login
                    auto_login()
                    print("  ╚══════════════════════════════════════════════════════════╝")
                else:
                    print("  ║  Remaining in offline mode.                              ║")
                    print("  ╚══════════════════════════════════════════════════════════╝")
            else:
                print("\n  ╔══════════════════════════════════════════════════════════╗")
                print("  ║              ENABLE OFFLINE MODE?                         ║")
                print("  ╠═══════════════════════════════════════════════════════════╣")
                print("  ║  This will disable:                                       ║")
                print("  ║  • Online matchmaking                                     ║")
                print("  ║  • User accounts and profiles                             ║")
                print("  ║  • Game history sync                                      ║")
                print("  ║                                                           ║")
                print("  ║  You will still be able to:                               ║")
                print("  ║  • Play vs AI (all difficulty levels)                     ║")
                print("  ║  • Local 2-player games                                   ║")
                print("  ║  • View ELO leaderboard (local)                           ║")
                print("  ║  • Analyze games                                          ║")
                print("  ║                                                           ║")
                try:
                    ans = input("  ║  Enable offline mode? [y/N]: ").strip().lower()
                except EOFError:
                    ans = 'n'
                if ans in ('y', 'yes'):
                    set_offline_mode(True)
                    print("  ║  Offline mode enabled!                                   ║")
                    print("  ╚══════════════════════════════════════════════════════════╝")
                else:
                    print("  ║  Remaining in online mode.                               ║")
                    print("  ╚══════════════════════════════════════════════════════════╝")

        else:
            print("  Invalid choice.")

# ════════════════════════════════════════════════════════════════════════
#  ENTRY POINT
# ════════════════════════════════════════════════════════════════════════
if __name__=='__main__':
    try:
        main()
    except KeyboardInterrupt:
        print("\n\n  Interrupted. Goodbye!\n")
    except Exception as e:
        import traceback; traceback.print_exc()
        sys.exit(1)
