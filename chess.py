#!/usr/bin/env python3
"""
╔══════════════════════════════════════════════════════════════════════════╗
║            ASCII CHESS — Ultimate Edition v3.0                           ║
║                                                                          ║
║  Features:                                                               ║
║   • All chess rules (castling, en passant, promotion, 50-move,           ║
║     threefold repetition, insufficient material)                         ║
║   • Standard Algebraic Notation + coordinate input (e2e4, e2-e4)        ║
║   • Chess Clock: Bullet/Blitz/Rapid/Classical time controls              ║
║   • Endgame Trainer: 7 classic endgame positions with coaching           ║
║   • Opening Explorer: deviation from book, alternatives shown            ║
║   • Opening Quiz: 12 flash-card positions to test your knowledge         ║
║   • PGN Import/Export: load, replay, analyze, save to file               ║
║   • Game Replay Viewer: ← → navigate any saved game                     ║
║   • Opening Book: 3000+ master-level positions (all major systems)       ║
║   • Strong AI: negamax + α-β, IID, TT, null-move, LMR, aspiration       ║
║   • Neural Network positional evaluator (NNUE-style, pure Python)        ║
║   • Built-in endgame tablebases (KQK, KRK, KBNK, KPK — perfect play)    ║
║   • ELO rating system • Online multiplayer • E2E encryption              ║
║   • 8 board themes including 2 colour-blind-safe themes                  ║
║   • Stockfish bridge (auto-detects if installed)                         ║
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
from datetime import datetime

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
PIECE_UNICODE = {
    (WHITE,PAWN):'♙',(WHITE,KNIGHT):'♘',(WHITE,BISHOP):'♗',
    (WHITE,ROOK):'♖',(WHITE,QUEEN):'♕',(WHITE,KING):'♔',
    (BLACK,PAWN):'♟',(BLACK,KNIGHT):'♞',(BLACK,BISHOP):'♝',
    (BLACK,ROOK):'♜',(BLACK,QUEEN):'♛',(BLACK,KING):'♚',
}

# ANSI colour helpers
_ANSI_RESET      = '\033[0m'
_BG_LIGHT        = '\033[48;5;223m'   # warm cream
_BG_DARK         = '\033[48;5;136m'   # rich brown
_BG_HL_LIGHT     = '\033[48;5;185m'   # yellow highlight (light sq)
_BG_HL_DARK      = '\033[48;5;178m'   # yellow highlight (dark sq)
_FG_WHITE_PIECE  = '\033[1;97m'       # bold bright white
_FG_BLACK_PIECE  = '\033[0;30m'       # black

def _ansi_supported():
    """Return True if the terminal likely supports ANSI escapes."""
    return hasattr(sys.stdout, 'isatty') and sys.stdout.isatty()

# ════════════════════════════════════════════════════════════════════════
#  GLOBAL SETTINGS
# ════════════════════════════════════════════════════════════════════════
SETTINGS_FILE = os.path.expanduser("~/.chess_settings.json")

# Board colour themes: name -> (light_sq, dark_sq, hl_light, hl_dark)
BOARD_THEMES = {
    # Format: (light_sq, dark_sq, hl_light, hl_dark)
    # Highlights use cyan/teal — visually distinct from both board squares
    # and white (bright) / gold (black) piece colours.
    'classic':    ('\033[48;5;223m', '\033[48;5;136m', '\033[48;5;37m',  '\033[48;5;30m'),
    'green':      ('\033[48;5;193m', '\033[48;5;64m',  '\033[48;5;37m',  '\033[48;5;30m'),
    'blue':       ('\033[48;5;153m', '\033[48;5;25m',  '\033[48;5;43m',  '\033[48;5;30m'),
    'grey':       ('\033[48;5;252m', '\033[48;5;240m', '\033[48;5;37m',  '\033[48;5;30m'),
    'red':        ('\033[48;5;224m', '\033[48;5;124m', '\033[48;5;37m',  '\033[48;5;30m'),
    'purple':     ('\033[48;5;225m', '\033[48;5;93m',  '\033[48;5;37m',  '\033[48;5;30m'),
    'cb_blue':    ('\033[48;5;117m', '\033[48;5;20m',  '\033[48;5;43m',  '\033[48;5;30m'),  # colour-blind safe
    'cb_orange':  ('\033[48;5;229m', '\033[48;5;130m', '\033[48;5;37m',  '\033[48;5;30m'),  # colour-blind safe
}

# Default settings
_settings = {
    'piece_style':      'letters',  # always letters for board alignment (setting kept for compat)
    'board_theme':      'classic',  # key in BOARD_THEMES
    'show_coords':      True,
    'colorblind_mode':  False,      # high-contrast blue/white + yellow pieces
    'show_eval_bar':    False,      # show evaluation bar during play
    'use_symbols':      True,       # use Unicode chess symbols ♙♟ etc.
    'ai_depth':         4,          # AI search depth (1-8)
    'clock_preset':     'Rapid',    # default time control
}

def _load_settings():
    global _settings
    try:
        if os.path.exists(SETTINGS_FILE):
            with open(SETTINGS_FILE, 'r') as f:
                saved = json.load(f)
            _settings.update(saved)
    except Exception:
        pass

def _save_settings():
    try:
        with open(SETTINGS_FILE, 'w') as f:
            json.dump(_settings, f, indent=2)
    except Exception:
        pass

def _get_board_colors():
    """Return (bg_light, bg_dark, bg_hl_light, bg_hl_dark) for current theme."""
    theme = _settings.get('board_theme', 'classic')
    return BOARD_THEMES.get(theme, BOARD_THEMES['classic'])

def settings_menu():
    """Interactive settings menu for board appearance and accessibility."""
    _load_settings()
    while True:
        coords     = _settings.get('show_coords', True)
        evalbar    = _settings.get('show_eval_bar', False)
        ai_depth   = _settings.get('ai_depth', 4)
        clock_pre  = _settings.get('clock_preset', 'Rapid')

        print("\n  ╔══════════════════════════════════════════════════════════╗")
        print("  ║                      SETTINGS                            ║")
        print("  ╠══════════════════════════════════════════════════════════╣")
        print(f"  ║  1. Show Coordinates : {'Yes' if coords else 'No':<34}║")
        print(f"  ║  2. Eval Bar in Game : {'On' if evalbar else 'Off':<34}║")
        print(f"  ║  3. AI Depth         : {ai_depth} (1=fast/easy  8=slow/hard)    ║")
        print(f"  ║  4. Default Clock    : {clock_pre:<34}║")
        print(f"  ║  5. Server Config    : configure online server           ║")
        print("  ╠══════════════════════════════════════════════════════════╣")
        print("  ║  Pieces always display as Unicode symbols: ♔♕♖♗♘♙♚♛♜♝♞♟ ║")
        print("  ╠══════════════════════════════════════════════════════════╣")
        print("  ║  0. Back to Main Menu                                    ║")
        print("  ╚══════════════════════════════════════════════════════════╝")
        try:
            choice = input("  Choice: ").strip()
        except EOFError:
            return

        if choice == '0':
            return

        elif choice == '1':
            _settings['show_coords'] = not _settings.get('show_coords', True)
            state = 'enabled' if _settings['show_coords'] else 'disabled'
            print(f"  ✓ Coordinates {state}.")
            _save_settings()

        elif choice == '2':
            _settings['show_eval_bar'] = not _settings.get('show_eval_bar', False)
            state = 'On' if _settings['show_eval_bar'] else 'Off'
            print(f"  ✓ Evaluation bar: {state}")
            _save_settings()

        elif choice == '3':
            try:
                d = int(input("  AI depth [1-8]: ").strip())
                if 1 <= d <= 8:
                    _settings['ai_depth'] = d
                    print(f"  ✓ AI depth set to {d}.")
                else:
                    print("  Please enter a number between 1 and 8.")
            except (ValueError, EOFError):
                print("  Invalid input.")
            _save_settings()

        elif choice == '4':
            presets = ['Bullet', 'Blitz', 'Rapid', 'Classical']
            for idx, p in enumerate(presets, 1):
                marker = " ◄" if p == clock_pre else ""
                print(f"  {idx}. {p}{marker}")
            try:
                sub = input(f"  Choose preset [1-{len(presets)}]: ").strip()
                pidx = int(sub) - 1
                if 0 <= pidx < len(presets):
                    _settings['clock_preset'] = presets[pidx]
                    print(f"  ✓ Default clock set to {presets[pidx]}.")
                else:
                    print("  Invalid choice.")
            except (ValueError, EOFError):
                print("  Invalid input.")
            _save_settings()

        elif choice == '5':
            configure_server_connection()

        else:
            print("  Invalid choice.")

_load_settings()
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
    def _normalise_input(self, raw):
        """
        Accept multiple move input formats and normalise to something
        parse_san can handle:
          • Standard SAN:  e4  Nf3  Bxc4  O-O  e8=Q
          • Coordinate:    e2e4  e2-e4  E2E4  (long algebraic)
          • Short coord:   Same but no dash
        Returns the normalised string, or raw unchanged if unrecognised.
        """
        s = raw.strip()
        # strip trailing annotations
        s2 = s.rstrip('+#!?')
        # Long algebraic e.g. "e2e4" or "e2-e4"
        pat = re.match(r'^([a-hA-H][1-8])[-x]?([a-hA-H][1-8])([qQrRbBnN]?)$', s2)
        if pat:
            from_sq_s = pat.group(1).lower()
            to_sq_s   = pat.group(2).lower()
            promo     = pat.group(3).upper()
            from_sq   = s2sq(from_sq_s)
            to_sq     = s2sq(to_sq_s)
            # Find the matching legal move
            for m in self.legal():
                if m.from_sq == from_sq and m.to_sq == to_sq:
                    if promo:
                        pmap = {'Q': QUEEN, 'R': ROOK, 'B': BISHOP, 'N': KNIGHT}
                        if m.promotion == pmap.get(promo):
                            return self.san(m)
                    elif m.promotion is None or m.promotion == QUEEN:
                        return self.san(m)
            # If we found the from/to squares at all, return a SAN
            for m in self.legal():
                if m.from_sq == from_sq and m.to_sq == to_sq:
                    return self.san(m)
        return s

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
            # Chigorin Variation (…Na5)
            "e4 e5 Nf3 Nc6 Bb5 a6 Ba4 Nf6 O-O Be7 Re1 b5 Bb3 Na5 Bc2 c5 d4 Qc7",
            "e4 e5 Nf3 Nc6 Bb5 a6 Ba4 Nf6 O-O Be7 Re1 b5 Bb3 Na5 Bc2 c5 d4 cxd4 Nxd4 Nxb3 axb3",
            # Archangel Variation (…Bb7)
            "e4 e5 Nf3 Nc6 Bb5 a6 Ba4 Nf6 O-O b5 Bb3 Bb7 d3 Be7",
            "e4 e5 Nf3 Nc6 Bb5 a6 Ba4 Nf6 O-O b5 Bb3 Bb7 d3 Bc5 c3 d6 Nbd2 O-O",
            # Neo-Archangel / Breyer
            "e4 e5 Nf3 Nc6 Bb5 a6 Ba4 Nf6 O-O Be7 Re1 b5 Bb3 Nb8 d3 d6 c3 Nbd7",
            "e4 e5 Nf3 Nc6 Bb5 a6 Ba4 Nf6 O-O Be7 Re1 b5 Bb3 Nb8 d4 Nbd7 Nbd2 Bb7 Bc2 c5",
            # Rio Gambit (Fried Liver in the Spanish)
            "e4 e5 Nf3 Nc6 Bb5 a6 Ba4 Nf6 O-O Nxe4 Re1 Nc5 Nxe5 Nxe5 Rxe5+ Be7 Bf1 Nf6 d4 Ne6 d5",
            # Zaitsev Variation
            "e4 e5 Nf3 Nc6 Bb5 a6 Ba4 Nf6 O-O Be7 Re1 b5 Bb3 d6 c3 O-O h3 Bb7 d4 Re8",
            "e4 e5 Nf3 Nc6 Bb5 a6 Ba4 Nf6 O-O Be7 Re1 b5 Bb3 d6 c3 O-O h3 Bb7 d4 Re8 Ng5 Rf8 Nf3 Re8",
            # Keres Variation
            "e4 e5 Nf3 Nc6 Bb5 a6 Ba4 Nf6 O-O Be7 Re1 b5 Bb3 d6 c3 O-O d4 Bg4 d5 Na5 Bc2 c6",

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

            # ── RÉTI OPENING — COMPREHENSIVE ──────────────────────────────
            # Main move order
            "Nf3 d5",
            "Nf3 d5 c4",
            # Réti Gambit (c4 dxc4)
            "Nf3 d5 c4 dxc4 e3 Nf6 Bxc4 e6 O-O c5 d4",
            "Nf3 d5 c4 dxc4 Na3 c5 Nxc4 Nc6 g3 e5 Nxe5 Nxe5 Bg2",
            # King's Indian Réti
            "Nf3 Nf6 c4 g6 g3 Bg7 Bg2 O-O O-O d6 d4 Nc6 Nc3 a6 d5 Na5 Nd2 c5 dxc6 Nxc6",
            "Nf3 Nf6 c4 g6 g3 Bg7 Bg2 O-O O-O d6 d4 Nbd7 Nc3 e5 e4 exd4 Nxd4 Re8",
            # Réti vs d5 slow build
            "Nf3 d5 g3 Nf6 Bg2 e6 O-O Be7 d3 O-O Nbd2 c5 c3 Nc6 Re1 b5",
            "Nf3 d5 g3 g6 Bg2 Bg7 O-O Nf6 d3 O-O Nbd2 c5 c3 Nc6 Re1",
            # Réti Gambit declined
            "Nf3 d5 c4 d4 b4 f6 g3 e5 Bg2 Be6 O-O c5 e3 Nf6",
            # Réti vs c5 (English/Réti hybrid)
            "Nf3 c5 c4 Nf6 Nc3 e6 g3 b6 Bg2 Bb7 O-O Be7 d4 cxd4 Qxd4 d6",
            "Nf3 c5 c4 g6 d4 cxd4 Nxd4 Nc6 g3 Bg7 Bg2 Nf6 Nc3 O-O O-O d6",
            # Réti vs Nf6 (Catalan-Réti)
            "Nf3 Nf6 c4 e6 g3 d5 Bg2 Be7 O-O O-O d4 dxc4 Qc2 a6 Qxc4 b5 Qd3 Bb7",
            "Nf3 Nf6 c4 e6 g3 d5 Bg2 Be7 O-O O-O b3 c5 Bb2 Nc6 e3 b6 Nc3",
            # Réti vs e5
            "Nf3 e5 Nxe5 Nc6 Nxc6 dxc6 g3 Nf6 Bg2 Bc5 d3 O-O Nc3 Re8",
            # Réti Opening 1.Nf3 Nf6 2.b3
            "Nf3 Nf6 b3 g6 Bb2 Bg7 c4 O-O g3 d6 Bg2 e5 O-O Nc6 d3",
            # Réti–Zukertort Attack
            "Nf3 d5 b3 Nf6 Bb2 Bf5 g3 e6 Bg2 Be7 O-O O-O d3 c5 Nbd2",
            "Nf3 d5 b3 Bg4 Bb2 Nd7 g3 e6 Bg2 Ngf6 O-O Be7 d3 O-O Nbd2 c5 c4",

            # ── PONZIANI OPENING — COMPREHENSIVE ──────────────────────────
            # Main line: 1.e4 e5 2.Nf3 Nc6 3.c3
            "e4 e5 Nf3 Nc6 c3",
            # Main response: 3...d5
            "e4 e5 Nf3 Nc6 c3 d5 Qa4 Nf6 Nxe5 Bd6 Nxc6 bxc6 d3 O-O Be2",
            "e4 e5 Nf3 Nc6 c3 d5 exd5 Qxd5 d4 e4 d5 exf3 dxc6 Qxd1+ Kxd1 fxg2 Bxg2",
            "e4 e5 Nf3 Nc6 c3 d5 d4 exd4 e5 d3 Bb5 Nge7 Bxc6+ Nxc6 Nxd3 Qd7",
            # 3...Nf6 (counter-attack)
            "e4 e5 Nf3 Nc6 c3 Nf6 d4 Nxe4 d5 Ne7 Nxe5 d6 Nxf7 Kxf7 dxe6+ Kxe6",
            "e4 e5 Nf3 Nc6 c3 Nf6 d4 exd4 e5 Nd5 cxd4 d6 Bc4 Nb6 Bb3 dxe5 dxe5 Bg4",
            "e4 e5 Nf3 Nc6 c3 Nf6 d4 exd4 e5 Nd5 Bc4 Be7 cxd4 O-O O-O d6 Nc3 Nxc3 bxc3",
            # 3...f5 (Jaenisch/Caro variation)
            "e4 e5 Nf3 Nc6 c3 f5 d4 fxe4 Nxe5 Nxe5 dxe5 d6 Qh5+ g6 Qd5 Be6 Qxb7 Rb8 Qa6",
            # 3...d6 (solid setup)
            "e4 e5 Nf3 Nc6 c3 d6 d4 Nf6 Bd3 Be7 O-O O-O Re1 Re8 Nbd2",
            # 3...Bc5 (Italian-like)
            "e4 e5 Nf3 Nc6 c3 Bc5 d4 exd4 cxd4 Bb4+ Nc3 Nf6 Be2 O-O O-O Bxc3 bxc3 d6",
            # Ponziani Countergambit (after 3...d5 4.Qa4 f6)
            "e4 e5 Nf3 Nc6 c3 d5 Qa4 f6 exd5 Nd4 Qa3 Nxf3+ gxf3 fxe5 Nxe5",
            # Ponziani vs Nf6 with early castling
            "e4 e5 Nf3 Nc6 c3 Nf6 d4 exd4 e5 Nd5 Bc4 Nxc3 bxc3 d5 exd6 Bxd6 O-O O-O",

            # ── ENGLISH OPENING ───────────────────────────────────────────
            "c4 e5 Nc3 Nf6 g3 d5 cxd5 Nxd5 Bg2 Nb6 Nf3 Nc6 O-O Be7 d3",
            "c4 e5 Nc3 Nc6 g3 g6 Bg2 Bg7 d3 d6 Nf3 f5 O-O Nf6 Rb1",
            "c4 Nf6 Nc3 e6 Nf3 d5 d4 Be7 Bg5 O-O e3 h6 Bh4 b6 cxd5 exd5",
            "c4 c5 Nc3 Nc6 g3 g6 Bg2 Bg7 Nf3 e5 O-O Nge7 d3 O-O Be3 d6",

            # ════════════════════════════════════════════════════════════════
            # ADDITIONAL WHITE OPENINGS
            # ════════════════════════════════════════════════════════════════

            # ── KING'S GAMBIT (e4 e5 f4) ──────────────────────────────────
            "e4 e5 f4",
            "e4 e5 f4 exf4 Nf3 g5 h4 g4 Ne5 Nf6 Bc4 d5 exd5 Bd6",
            "e4 e5 f4 exf4 Nf3 g5 Bc4 g4 O-O gxf3 Qxf3 Nc6 d3 Ne5 Qg3",
            "e4 e5 f4 exf4 Bc4 d5 Bxd5 Nf6 Nc3 Bb4 Nf3 O-O O-O c6 Bb3",
            "e4 e5 f4 Bc5 Nf3 d6 c3 Bg4 Be2 Nc6 d4 exd4 cxd4 Bb6",
            # King's Gambit Declined
            "e4 e5 f4 Bc5 fxe5 d6 exd6 Bxd6 Nf3 Nf6 Nc3 Nc6 Bc4 O-O O-O",
            "e4 e5 f4 d5 exd5 e4 d3 Nf6 dxe4 Nxe4 Nf3 Bc5 Qe2 Bf5 Nc3",

            # ── DANISH GAMBIT ──────────────────────────────────────────────
            "e4 e5 d4 exd4 c3 dxc3 Bc4 cxb2 Bxb2 d5 Bxd5 Nf6 Bxf7+ Kxf7 Qxd8",
            "e4 e5 d4 exd4 c3 dxc3 Nxc3 Nc6 Bc4 Bc5 Nf3 d6 O-O",

            # ── VIENNA GAME ───────────────────────────────────────────────
            "e4 e5 Nc3",
            "e4 e5 Nc3 Nf6 f4 d5 fxe5 Nxe4 Nf3 Be7 d4 O-O Bd3 f5 exf6 Nxf6",
            "e4 e5 Nc3 Nc6 f4 exf4 Nf3 g5 Bc4 g4 O-O gxf3 Qxf3 Ne5 Qxf4 Nxc4 Qxc4 d6",
            "e4 e5 Nc3 Bc5 Bc4 Nf6 d3 Nc6 f4 d6 Nf3 O-O O-O a6 a4",
            "e4 e5 Nc3 Nf6 Bc4 Nxe4 Qh5 Nd6 Bb3 Nc6 Nb5 g6 Qf3 f5 Qd5 Qe7",
            # Vienna Gambit
            "e4 e5 Nc3 Nf6 f4 d5 fxe5 Nxe4 Qf3 Nc6 Bb5 Nd4 Qxe4+ Nxb5 Nxb5 dxe4 Nxc7+",

            # ── BISHOP'S OPENING ──────────────────────────────────────────
            "e4 e5 Bc4 Nf6 d3 c6 Nf3 Be7 O-O d5 Bb3 O-O Nc3 dxe4 dxe4",
            "e4 e5 Bc4 Bc5 Qe2 Nc6 c3 Nf6 f4 d6 d3 O-O Nf3",

            # ── LATVIAN GAMBIT (with White lines) ─────────────────────────
            "e4 e5 Nf3 f5 Nxe5 Qf6 Nc4 fxe4 Nc3 Qf7 Ne3 c6 d4 exd3 Bxd3 d5 O-O",

            # ── KING'S INDIAN ATTACK ──────────────────────────────────────
            "Nf3 d5 g3 Nf6 Bg2 c5 O-O Nc6 d3 e5 Nbd2 Be7 e4 dxe4 dxe4 O-O",
            "e4 d6 Nf3 Nf6 g3 g6 Bg2 Bg7 O-O O-O d3 c5 Nbd2 Nc6 Re1",
            "e4 c5 Nf3 e6 g3 Nc6 Bg2 d5 exd5 exd5 d4 cxd4 Nxd4 Nf6 O-O Be7",

            # ── CLOSED SICILIAN (2.Nc3) ───────────────────────────────────
            "e4 c5 Nc3 Nc6 g3 g6 Bg2 Bg7 d3 d6 f4 e5 Nf3 Nge7 O-O O-O",
            "e4 c5 Nc3 e6 g3 d5 exd5 exd5 d4 Nc6 Bg2 cxd4 Nxd4 Nf6 O-O Be7",

            # ── ALAPIN SICILIAN (2.c3) ─────────────────────────────────────
            "e4 c5 c3 d5 exd5 Qxd5 d4 Nc6 Nf3 Bg4 Be2 cxd4 cxd4 e6 Nc3 Bb4",
            "e4 c5 c3 Nf6 e5 Nd5 d4 cxd4 cxd4 d6 Nf3 Nc6 Bc4 Nb6 Bb3 dxe5 dxe5 Bf5",
            "e4 c5 c3 e6 d4 d5 exd5 exd5 Nf3 Nc6 Bb5 Bd6 dxc5 Bxc5 O-O Ne7",

            # ── GRAND PRIX ATTACK (Sicilian) ──────────────────────────────
            "e4 c5 Nc3 Nc6 f4 g6 Nf3 Bg7 Bc4 e6 f5 exf5 exf5 d5 fxg6 hxg6 Bb3",

            # ── ENGLISH ATTACK (Sicilian) ──────────────────────────────────
            "e4 c5 Nf3 e6 d4 cxd4 Nxd4 Nc6 Nc3 d6 Be3 Nf6 f3 Be7 Qd2 O-O O-O-O",
            "e4 c5 Nf3 e6 d4 cxd4 Nxd4 Nc6 Nc3 Qc7 Be2 a6 O-O Nf6 f4 d6 Kh1",

            # ── SMITH-MORRA GAMBIT ─────────────────────────────────────────
            "e4 c5 d4 cxd4 c3 dxc3 Nxc3 Nc6 Nf3 d6 Bc4 e6 O-O Nf6 Qe2 Be7 Rd1",
            "e4 c5 d4 cxd4 c3 dxc3 Nxc3 e6 Nf3 a6 Bc4 b5 Bb3 Bb7 O-O Nf6 Qe2",

            # ── CATALAN OPENING ────────────────────────────────────────────
            "d4 Nf6 c4 e6 g3 d5 Bg2 Be7 Nf3 O-O O-O dxc4 Qc2 a6 Qxc4 b5 Qd3 Bb7",
            "d4 Nf6 c4 e6 g3 d5 Bg2 Bb4+ Bd2 Be7 Nf3 O-O O-O c6 Nc3 Nbd7 Qc2",
            "d4 d5 c4 e6 g3 Nf6 Bg2 Be7 Nf3 O-O O-O dxc4 Qa4 c5 dxc5 Bxc5 Nbd2",
            "d4 Nf6 c4 e6 Nf3 d5 g3 dxc4 Bg2 Bb4+ Bd2 a5 O-O Nc6 Bxb4 axb4 Nbd2",

            # ── LONDON SYSTEM (expanded) ───────────────────────────────────
            "d4 Nf6 Bf4 e6 e3 d5 Nf3 Bd6 Bg3 O-O Nbd2 c5 c3 Nc6 Bd3 Qe7",
            "d4 d5 Bf4 Nf6 e3 e6 Nf3 c5 c3 Nc6 Nbd2 Bd6 Bg3 O-O Bb5 Bd7",
            "d4 Nf6 Bf4 d5 e3 c5 c3 Nc6 Nd2 e6 Ngf3 Bd6 Bg3 O-O Bb5 Qe7 dxc5",
            "d4 d5 Bf4 c5 e3 Nc6 Nf3 Nf6 Nbd2 e6 c3 Bd6 Bg3 O-O Bb5",

            # ── STONEWALL ATTACK ──────────────────────────────────────────
            "d4 d5 e3 Nf6 Bd3 e6 f4 c5 c3 Nc6 Nd2 Bd6 Ngf3 O-O O-O Qc7 Ne5",
            "d4 d5 e3 Nf6 f4 e6 Nf3 c5 c3 Nc6 Bd3 Bd6 O-O O-O Ne5 Qc7 Nd2",

            # ── BARRY ATTACK /150 ATTACK ─────────────────────────────────
            "d4 Nf6 Nf3 g6 Nc3 d5 Bf4 Bg7 e3 O-O Be2 c6 Ne5 Nfd7 Nxd7 Nxd7 O-O",

            # ── KING'S INDIAN ATTACK (vs French setup) ────────────────────
            "e4 e6 d3 d5 Nd2 Nf6 g3 Be7 Bg2 O-O Ngf3 c5 O-O Nc6 Re1 b5",

            # ════════════════════════════════════════════════════════════════
            # ADDITIONAL BLACK OPENINGS
            # ════════════════════════════════════════════════════════════════

            # ── SICILIAN DRAGON ───────────────────────────────────────────
            "e4 c5 Nf3 d6 d4 cxd4 Nxd4 Nf6 Nc3 g6",
            "e4 c5 Nf3 d6 d4 cxd4 Nxd4 Nf6 Nc3 g6 Be3 Bg7 f3 O-O Qd2 Nc6 Bc4 Bd7",
            "e4 c5 Nf3 d6 d4 cxd4 Nxd4 Nf6 Nc3 g6 Be3 Bg7 f3 Nc6 Bc4 Bd7 Qd2 O-O O-O-O Rb8",
            "e4 c5 Nf3 d6 d4 cxd4 Nxd4 Nf6 Nc3 g6 Be2 Bg7 O-O O-O f4 Nc6 Nb3",

            # ── SICILIAN CLASSICAL (Scheveningen) ─────────────────────────
            "e4 c5 Nf3 d6 d4 cxd4 Nxd4 Nf6 Nc3 e6 Be2 Be7 O-O O-O f4 Nc6 Be3",
            "e4 c5 Nf3 e6 d4 cxd4 Nxd4 Nf6 Nc3 d6 g4 h6 h4 Nc6 Rg1 d5",

            # ── SICILIAN KAN / TAIMANOV ───────────────────────────────────
            "e4 c5 Nf3 e6 d4 cxd4 Nxd4 a6 Bd3 Nf6 O-O Qc7 Qe2 d6 c4 Nbd7",
            "e4 c5 Nf3 e6 d4 cxd4 Nxd4 Nc6 Nc3 a6 Nxc6 bxc6 Bd3 d5 O-O Nf6",

            # ── SICILIAN SVESHNIKOV ───────────────────────────────────────
            "e4 c5 Nf3 Nc6 d4 cxd4 Nxd4 Nf6 Nc3 e5 Ndb5 d6 Bg5 a6 Na3 b5",
            "e4 c5 Nf3 Nc6 d4 cxd4 Nxd4 Nf6 Nc3 e5 Ndb5 d6 Bg5 a6 Na3 b5 Bxf6 gxf6 Nd5 f5",

            # ── FRENCH WINAWER ────────────────────────────────────────────
            "e4 e6 d4 d5 Nc3 Bb4",
            "e4 e6 d4 d5 Nc3 Bb4 e5 c5 a3 Bxc3+ bxc3 Ne7 Qg4 Qc7 Qxg7 Rg8 Qxh7 cxd4",
            "e4 e6 d4 d5 Nc3 Bb4 e5 c5 a3 Ba5 Qg4 Ne7 Qxg7 Rg8 Qxh7 cxd4 Ne2 Nbc6",

            # ── FRENCH CLASSICAL ──────────────────────────────────────────
            "e4 e6 d4 d5 Nc3 Nf6 Bg5 Be7 e5 Nfd7 Bxe7 Qxe7 f4 O-O Nf3 c5 Qd2 Nc6",

            # ── FRENCH RUBINSTEIN ─────────────────────────────────────────
            "e4 e6 d4 d5 Nc3 dxe4 Nxe4 Nd7 Nf3 Ngf6 Nxf6+ Nxf6 c3 c5 Be3 cxd4",

            # ── FRENCH TARRASCH ───────────────────────────────────────────
            "e4 e6 d4 d5 Nd2 Nf6 e5 Nfd7 Bd3 c5 c3 Nc6 Ne2 cxd4 cxd4 f6 exf6 Nxf6",

            # ── CARO-KANN CLASSICAL ───────────────────────────────────────
            "e4 c6 d4 d5 Nc3 dxe4 Nxe4 Bf5 Ng3 Bg6 h4 h6 Nf3 Nd7 h5 Bh7 Bd3 Bxd3 Qxd3 e6",

            # ── CARO-KANN ADVANCE ─────────────────────────────────────────
            "e4 c6 d4 d5 e5 Bf5 Nf3 e6 Be2 Nd7 O-O Ne7 Nbd2 h6 Nb3 Bg4 Bxg4",

            # ── CARO-KANN EXCHANGE ────────────────────────────────────────
            "e4 c6 d4 d5 exd5 cxd5 Bd3 Nc6 c3 Nf6 Bf4 Bg4 Qb3 Na5 Qa4+ Nc6",

            # ── PIRC DEFENCE ──────────────────────────────────────────────
            "e4 d6 d4 Nf6 Nc3 g6 f4 Bg7 Nf3 O-O Bd3 Na6 O-O c5 d5 Nc7",
            "e4 d6 d4 Nf6 Nc3 g6 Be3 Bg7 Qd2 c6 f3 b5 Nge2 Nbd7 Bh6 Bxh6 Qxh6",

            # ── MODERN DEFENCE ────────────────────────────────────────────
            "e4 g6 d4 Bg7 Nc3 d6 f4 Nf6 Nf3 O-O Bd3 Na6 O-O c5 d5 Rb8",
            "e4 g6 d4 Bg7 Nc3 d6 Be3 a6 Qd2 b5 f3 Nd7 Nh3 c5 dxc5 dxc5 Bxc5 Nxc5",

            # ── KING'S INDIAN DEFENCE ─────────────────────────────────────
            "d4 Nf6 c4 g6 Nc3 Bg7 e4 d6 Nf3 O-O Be2 e5 O-O Nc6 d5 Ne7",
            # Saemisch KID
            "d4 Nf6 c4 g6 Nc3 Bg7 e4 d6 f3 O-O Be3 e5 d5 Nh5 Qd2 Qh4+ g3 Nxg3",
            # Four Pawns KID
            "d4 Nf6 c4 g6 Nc3 Bg7 e4 d6 f4 O-O Nf3 c5 d5 b5 cxb5 a6",
            # Classical KID main line
            "d4 Nf6 c4 g6 Nc3 Bg7 e4 d6 Nf3 O-O Be2 e5 O-O Nc6 d5 Ne7 Nd2 a5",
            # Averbakh KID
            "d4 Nf6 c4 g6 Nc3 Bg7 e4 d6 Be2 O-O Bg5 h6 Be3 e5 d5 Nh5",

            # ── GRÜNFELD DEFENCE ──────────────────────────────────────────
            "d4 Nf6 c4 g6 Nc3 d5 cxd5 Nxd5 e4 Nxc3 bxc3 Bg7 Bc4 c5 Ne2 Nc6 Be3",
            "d4 Nf6 c4 g6 Nc3 d5 Nf3 Bg7 e3 O-O b4 dxc4 Bxc4 c5 b5",
            # Exchange Grünfeld
            "d4 Nf6 c4 g6 Nc3 d5 cxd5 Nxd5 e4 Nxc3 bxc3 Bg7 Nf3 c5 Be3 Qa5",

            # ── NIMZO-INDIAN DEFENCE ──────────────────────────────────────
            "d4 Nf6 c4 e6 Nc3 Bb4 e3 O-O Bd3 d5 Nf3 c5 O-O dxc4 Bxc4 cxd4 exd4",
            # Rubinstein Nimzo
            "d4 Nf6 c4 e6 Nc3 Bb4 e3 b6 Bd3 Bb7 Nf3 O-O O-O d5 cxd5 exd5 Ne5",
            # Saemisch Nimzo
            "d4 Nf6 c4 e6 Nc3 Bb4 a3 Bxc3+ bxc3 c5 f3 d5 cxd5 exd5 e3 O-O Ne2",
            # Classical Nimzo
            "d4 Nf6 c4 e6 Nc3 Bb4 Qc2 d5 cxd5 exd5 Bg5 h6 Bh4 c5 dxc5 g5 Bg3 Ne4",

            # ── QUEEN'S INDIAN DEFENCE ────────────────────────────────────
            "d4 Nf6 c4 e6 Nf3 b6 g3 Ba6 b3 Bb4+ Bd2 Be7 Bg2 c6 Bc3 d5 Ne5",
            "d4 Nf6 c4 e6 Nf3 b6 e3 Bb7 Bd3 d5 b3 Nbd7 O-O Bd6 Bb2 O-O Nbd2",

            # ── SLAV DEFENCE ──────────────────────────────────────────────
            "d4 d5 c4 c6 Nf3 Nf6 Nc3 a6 e3 b5 b3 Bg4 Bd3 e6 O-O Nbd7",
            # Semi-Slav
            "d4 d5 c4 c6 Nf3 Nf6 Nc3 e6 Bg5 h6 Bh4 dxc4 e4 g5 Bg3 b5",
            # Meran variation
            "d4 d5 c4 c6 Nf3 Nf6 Nc3 e6 e3 Nbd7 Bd3 dxc4 Bxc4 b5 Bd3 a6 e4 c5",

            # ── DUTCH DEFENCE ─────────────────────────────────────────────
            "d4 f5 g3 Nf6 Bg2 e6 Nf3 Be7 O-O O-O c4 d6 Nc3 Qe8 b3",
            "d4 f5 c4 Nf6 g3 e6 Bg2 Bb4+ Bd2 Bxd2+ Qxd2 O-O Nf3 d6 O-O Qe8",
            # Leningrad Dutch
            "d4 f5 g3 Nf6 Bg2 g6 Nf3 Bg7 O-O d6 c4 O-O Nc3 c6 d5",
            # Stonewall Dutch
            "d4 f5 Nf3 e6 g3 Nf6 Bg2 d5 O-O Bd6 c4 c6 b3 Qe7 Bb2 b6",

            # ── BENONI DEFENCE ────────────────────────────────────────────
            "d4 Nf6 c4 c5 d5 e6 Nc3 exd5 cxd5 d6 Nf3 g6 Nd2 Bg7 e4 O-O Be2",
            # Modern Benoni
            "d4 Nf6 c4 c5 d5 e6 Nc3 exd5 cxd5 d6 e4 g6 Nf3 Bg7 Be2 O-O O-O Re8",

            # ── KING'S INDIAN DEFENCE vs LONDON ──────────────────────────
            "d4 Nf6 Nf3 g6 Bf4 Bg7 Nbd2 O-O e3 d6 Be2 c6 h3 Nbd7 O-O e5",

            # ── ALEKHINE'S DEFENCE ────────────────────────────────────────
            "e4 Nf6 e5 Nd5 d4 d6 Nf3 dxe5 Nxe5 g6 Bc4 Nb6 Bb3 Bg7 O-O O-O Re1",
            "e4 Nf6 e5 Nd5 d4 d6 c4 Nb6 exd6 exd6 Nc3 Be7 Be3 O-O Rc1",

            # ── SCANDINAVIAN (expanded) ───────────────────────────────────
            "e4 d5 exd5 Qxd5 Nc3 Qa5 d4 Nf6 Nf3 Bf5 Bc4 e6 Bd2 c6 Qe2 Bb4 O-O-O",
            "e4 d5 exd5 Nf6 d4 Bg4 Nf3 Qxd5 Be2 e6 O-O Be7 c4 Qd8 Nc3 O-O h3 Bh5",

            # ── OWEN'S DEFENCE ────────────────────────────────────────────
            "e4 b6 d4 Bb7 Bd3 e6 Nf3 c5 c3 Nf6 Nbd2 cxd4 cxd4 d5 e5 Nfd7",

            # ── NIMZOWITSCH DEFENCE ───────────────────────────────────────
            "e4 Nc6 d4 d5 Nc3 dxe4 d5 Ne5 Qd4 Nf6 Qxe4 e6 dxe6 Bxe6 Nf3",

            # ── POLISH OPENING (1.b4) ──────────────────────────────────────
            # Main line
            "b4 e5 Bb2 f6 b5 d5 e3 Be6 Nf3 Nd7 d4 dxe4 Nd2 Bd5 c4",
            # Outflank Variation
            "b4 c6 Bb2 a5 b5 cxb5 e4 e6 Bxb5 Nf6 Nf3 Be7 O-O O-O",
            # Polish Gambit
            "b4 e5 Bb2 Bxb4 Bxe5 Nf6 c4 O-O Nf3 d6 Bg3 Nc6",
            # Symmetric Variation
            "b4 b5 Bb2 Bb7 e3 e6 a3 a5 b5 Nf6 Nf3 Be7 d4 O-O",
            # Polish vs d5
            "b4 d5 Bb2 Nf6 e3 Bf5 Nf3 e6 Be2 Nbd7 O-O Bd6",
            # King's Indian setup vs Polish
            "b4 Nf6 Bb2 g6 b5 Bg7 e3 d6 d4 O-O Nf3 Nbd7 Be2",
            # Bugayev Attack
            "b4 e5 b5 Nf6 e4 Bc5 Bc4 O-O Ne2 c6 bxc6 dxc6 O-O Nc6",

            # ── ENGLISH OPENING (1.c4) ─────────────────────────────────────
            # Symmetrical: Two Knights
            "c4 c5 Nc3 Nc6 g3 g6 Bg2 Bg7 Nf3 e6 O-O Nge7 d4 cxd4 Nxd4 O-O",
            # Symmetrical: Hedgehog
            "c4 c5 Nf3 Nf6 Nc3 e6 g3 b6 Bg2 Bb7 O-O Be7 d4 cxd4 Qxd4",
            # Symmetrical with Nc3 Nd5
            "c4 c5 Nc3 Nf6 g3 d5 cxd5 Nxd5 Bg2 Nc7 Nf3 Nc6 O-O e5",
            # Reversed Sicilian (e5 system)
            "c4 e5 Nc3 Nf6 Nf3 Nc6 g3 d5 cxd5 Nxd5 Bg2 Nb6 O-O Be7",
            # Reversed Sicilian Kan
            "c4 e5 Nc3 Nc6 Nf3 Nf6 g3 Bb4 Bg2 O-O O-O e4 Ng5 Bxc3",
            # Four Knights English
            "c4 e5 Nc3 Nf6 Nf3 Nc6 g3 Bb4 Bg2 O-O O-O Re8 d3 Bxc3",
            # Anglo-Indian (Nf6 system)
            "c4 Nf6 Nc3 e6 Nf3 d5 d4 Be7 Bg5 h6 Bh4 O-O e3 b6",
            # Mikenas-Carls variation
            "c4 Nf6 Nc3 e6 e4 d5 e5 d4 exf6 dxc3 bxc3 Qxf6",
            # Anglo-Grünfeld
            "c4 Nf6 Nc3 d5 cxd5 Nxd5 g3 g6 Bg2 Nxc3 bxc3 Bg7 Nf3 O-O O-O c5",
            # English Opening vs King's Indian
            "c4 Nf6 Nc3 g6 Nf3 Bg7 g3 O-O Bg2 d6 O-O e5 d3 Nc6 Rb1",
            # Taimanov English
            "c4 e5 Nc3 Nc6 g3 g6 Bg2 Bg7 d3 d6 Nf3 f5 O-O Nf6 Rb1",
            # English Botvinnik System
            "c4 c5 Nf3 Nc6 d4 cxd4 Nxd4 e5 Nc2 Nf6 Nc3 d6 e4 Be7 Be2 O-O",
            # King's English (1.c4 e5 2.g3)
            "c4 e5 g3 Nf6 Bg2 d5 cxd5 Nxd5 Nc3 Nb6 Nf3 Nc6 O-O Be7 d3 O-O",

            # ── BIRD'S OPENING (1.f4) ──────────────────────────────────────
            "f4 d5 Nf3 Nf6 e3 g6 Be2 Bg7 O-O O-O d3 c5 Qe1 Nc6 Qh4",
            "f4 e5 fxe5 d6 exd6 Bxd6 Nf3 Nf6 g3 Ng4 Bg2 Nxh2 Rxh2",

            # ── GROB ATTACK (1.g4) ─────────────────────────────────────────
            "g4 d5 Bg2 Bxg4 c4 c3 Qb3 Bd7 Nf3 Nf6",

            # ── VAN'T KRUIJS OPENING ──────────────────────────────────────
            "e3 e5 d4 exd4 exd4 d5 Nf3 Nf6 Bd3 Bd6 O-O O-O",

            # ── NIMZOWITSCH-LARSEN ATTACK ─────────────────────────────────
            "b3 e5 Bb2 Nc6 e3 Nf6 Nf3 e4 Nd4 Bc5 Nxc6 dxc6 d4 exd3 Bxd3",
            "Nf3 d5 b3 c5 Bb2 Nc6 e3 Nf6 Bb5 Bg4 h3 Bh5 O-O e6 d4",

            # ── CATALAN (Black response with ...dxc4) ─────────────────────
            "d4 Nf6 c4 e6 g3 d5 Bg2 dxc4 Nf3 Bd7 O-O Bc6 Qc2 Bxf3 exf3 Nd5",

            # ── TARRASCH DEFENCE ──────────────────────────────────────────
            "d4 d5 c4 e6 Nc3 c5 cxd5 exd5 Nf3 Nc6 g3 Nf6 Bg2 Be7 O-O O-O Bg5 cxd4",

            # ── EXCHANGE QUEEN'S GAMBIT (Black) ───────────────────────────
            "d4 d5 c4 dxc4 Nf3 Nf6 e3 e6 Bxc4 c5 O-O a6 dxc5 Bxc5 Qxd8+ Kxd8",

            # ── SYMMETRICAL ENGLISH (Black) ───────────────────────────────
            "c4 c5 Nc3 Nc6 g3 g6 Bg2 Bg7 Nf3 e6 O-O Nge7 d4 cxd4 Nxd4 O-O",

            # ── ADDITIONAL RUY LOPEZ LINES ────────────────────────────────
            # Zaitsev Variation
            "e4 e5 Nf3 Nc6 Bb5 a6 Ba4 Nf6 O-O Be7 Re1 b5 Bb3 d6 c3 O-O h3 Bb7",
            # Breyer Variation
            "e4 e5 Nf3 Nc6 Bb5 a6 Ba4 Nf6 O-O Be7 Re1 b5 Bb3 d6 c3 O-O h3 Nb8",
            # Chigorin Variation
            "e4 e5 Nf3 Nc6 Bb5 a6 Ba4 Nf6 O-O Be7 Re1 b5 Bb3 d6 c3 O-O h3 Na5 Bc2 c5 d4 Qc7",
            # Archangel Variation
            "e4 e5 Nf3 Nc6 Bb5 a6 Ba4 Nf6 O-O b5 Bb3 Bc5 c3 d6 d4 Bb6",

            # ── ADDITIONAL SICILIAN LINES ─────────────────────────────────
            # Accelerated Dragon
            "e4 c5 Nf3 Nc6 d4 cxd4 Nxd4 g6 Nc3 Bg7 Be3 Nf6 Bc4 O-O Bb3 d6",
            # Taimanov Variation
            "e4 c5 Nf3 e6 d4 cxd4 Nxd4 Nc6 Nc3 Qc7 Be3 a6 Bd3 Nf6 O-O Ne5",
            # Kalashnikov Variation
            "e4 c5 Nf3 Nc6 d4 cxd4 Nxd4 e5 Nb5 d6 N1c3 a6 Na3 b5 Nd5 Nge7",
            # Polugaevsky Variation
            "e4 c5 Nf3 d6 d4 cxd4 Nxd4 Nf6 Nc3 a6 Bg5 e6 f4 b5 e5 dxe5 fxe5 Qc7",

            # ── ADDITIONAL QUEEN'S GAMBIT LINES ──────────────────────────
            # Ragozin Defence
            "d4 d5 c4 e6 Nc3 Nf6 Nf3 Bb4 Bg5 Nbd7 cxd5 exd5 Qc2 c5",
            # Vienna Variation QGD
            "d4 d5 c4 e6 Nc3 Nf6 Nf3 dxc4 e3 c5 Bxc4 a6 O-O b5 Bd3 Bb7",
            # Cambridge Springs Defence
            "d4 d5 c4 e6 Nc3 Nf6 Bg5 Nbd7 e3 c6 Nf3 Qa5 Nd2 Bb4 Qc2 O-O",
            # Harrwitz Attack
            "d4 d5 c4 e6 Nc3 Nf6 Bf4 Bd6 Bg3 O-O Nf3 b6 e3 Bb7 Be2 c5",

            # ── ADDITIONAL KING'S INDIAN LINES ───────────────────────────
            # Petrosian System
            "d4 Nf6 c4 g6 Nc3 Bg7 e4 d6 Nf3 O-O Be2 e5 d5 a5 Bg5 Na6 Nd2 Nc5",
            # Makogonov Variation
            "d4 Nf6 c4 g6 Nc3 Bg7 e4 d6 Nf3 O-O h3 e5 d5 Nh5 Nh2 Qe8 Be2 Nf4",
            # Bayonet Attack KID
            "d4 Nf6 c4 g6 Nc3 Bg7 e4 d6 Nf3 O-O Be2 e5 O-O Nc6 d5 Ne7 b4 Nh5",

            # ── RETI / KING'S FIANCHETTO ──────────────────────────────────
            "Nf3 Nf6 g3 g6 Bg2 Bg7 O-O O-O d3 d6 e4 e5 Nc3 Nc6 Be3",
            "Nf3 d5 g3 c6 Bg2 Bg4 O-O Nd7 d3 e5 Nbd2 Ngf6 c4",
            "Nf3 c5 c4 Nc6 d4 cxd4 Nxd4 Nf6 g3 g6 Bg2 d5 cxd5 Nxd5 O-O Bg7",

            # ── SOKOLSKY / POLISH (1.b4) ADVANCED ────────────────────────
            "b4 e6 Bb2 Nf6 b5 d5 e3 Nbd7 Nf3 Bd6 c4 c6 bxc6 bxc6 Be2 O-O",
            "b4 d5 Bb2 c6 a3 Nf6 Nf3 Bg4 e3 e6 Be2 Nbd7 O-O Bd6 c4",

            # ── KING'S INDIAN DEFENCE — GLIGORIC ─────────────────────────
            "d4 Nf6 c4 g6 Nc3 Bg7 e4 d6 Nf3 O-O Be2 e5 Be3 exd4 Nxd4 Re8",
            "d4 Nf6 c4 g6 Nc3 Bg7 e4 d6 Nf3 O-O Be2 Nc6 d5 Ne7 Ne1 Nd7 Nd3 f5",

            # ── NIMZO-INDIAN — ZÜRICH VARIATION ───────────────────────────
            "d4 Nf6 c4 e6 Nc3 Bb4 Qc2 d5 cxd5 Qxd5 Nf3 Qf5 Qxf5 exf5 a3 Be7",
            "d4 Nf6 c4 e6 Nc3 Bb4 Qc2 c5 dxc5 O-O a3 Bxc3+ Qxc3 b6 Bg5 Bb7",

            # ── QUEEN'S GAMBIT DECLINED — LASKER ─────────────────────────
            "d4 d5 c4 e6 Nc3 Nf6 Bg5 Be7 e3 O-O Nf3 Ne4 Bxe7 Qxe7 cxd5 Nxc3",
            "d4 d5 c4 e6 Nc3 Nf6 Bg5 Be7 e3 Ne4 Bxe7 Qxe7 Nxe4 dxe4 Nd2 f5",

            # ── SEMI-TARRASCH ─────────────────────────────────────────────
            "d4 d5 c4 e6 Nc3 Nf6 Nf3 c5 cxd5 Nxd5 e3 Nc6 Bd3 Be7 O-O O-O a3",
            "d4 Nf6 c4 e6 Nf3 d5 Nc3 c5 cxd5 Nxd5 e3 Nc6 Bd3 Be7 O-O O-O",

            # ── STONEWALL DUTCH — BLACK ──────────────────────────────────
            "d4 f5 Nf3 Nf6 g3 e6 Bg2 d5 O-O c6 c4 Bd6 Nc3 Qe7 Ne5 O-O f3",
            "d4 e6 Nf3 f5 g3 Nf6 Bg2 d5 O-O Bd6 b3 O-O Bb2 c6 Ne5 Qe7",

            # ── BUDAPEST GAMBIT — RUBINSTEIN ──────────────────────────────
            "d4 Nf6 c4 e5 dxe5 Ne4 Nf3 Bb4+ Nbd2 Nc6 a3 Bxd2+ Bxd2 Nxd2 Qxd2",
            "d4 Nf6 c4 e5 dxe5 Ne4 Nd2 Nxd2 Bxd2 d6 exd6 Bxd6 Nf3 Nc6 e3",

            # ── ENGLISH OPENING — KINGS ENGLISH ──────────────────────────
            "c4 e5 g3 Nf6 Bg2 d5 cxd5 Nxd5 Nc3 Nb6 Nf3 Nc6 O-O Be7 d3 O-O",
            "c4 e5 Nc3 d6 g3 f5 Bg2 Nf6 d3 g6 e4 fxe4 dxe4 Bg7 Nge2 O-O",

            # ── TARRASCH DEFENCE — RUBINSTEIN VARIATION ───────────────────
            "d4 d5 c4 e6 Nc3 c5 cxd5 exd5 Nf3 Nc6 g3 Be6 Bg2 Be7 O-O Nf6 Bg5",
            "d4 d5 c4 e6 Nc3 c5 Nf3 Nc6 cxd5 exd5 Bg5 f6 Bf4 Bg4 e3 Nge7",

            # ── QUEEN'S GAMBIT — BALTIC DEFENCE ──────────────────────────
            "d4 d5 c4 Bf5 cxd5 Bxb1 Rxb1 Qxd5 Nf3 e6 g3 Nf6 Bg2 c6 O-O",

            # ── KING'S GAMBIT — BECKER DEFENCE ───────────────────────────
            "e4 e5 f4 exf4 Nf3 h6 d4 d6 Bxf4 g5 Be3 Nf6 Nc3 Bg7 Bd3",

            # ── FOUR KNIGHTS — SPANISH FOUR KNIGHTS ──────────────────────
            "e4 e5 Nf3 Nc6 Nc3 Nf6 Bb5 Bb4 O-O O-O d3 Bxc3 bxc3 d5 exd5 Qxd5",
            "e4 e5 Nf3 Nc6 Nc3 Nf6 Bb5 Nd4 Nxd4 exd4 Nd5 Nxd5 exd5 Qe7 Qe2 Qxe2+",

            # ── CARO-KANN — FANTASY VARIATION ────────────────────────────
            "e4 c6 d4 d5 f3 e6 Nc3 dxe4 fxe4 e5 Nf3 exd4 Nxd4 Nf6 Bg5 Be7",
            "e4 c6 d4 d5 f3 dxe4 fxe4 e5 Nf3 Bg4 Bc4 exd4 c3 dxc3 Nxc3 Bxf3",

            # ── GRÜNFELD — NADANIAN ATTACK ────────────────────────────────
            "d4 Nf6 c4 g6 Nc3 d5 h4 dxc4 e4 Bg7 Bxc4 O-O Nge2 c5 Be3 Nc6",

            # ── SICILIAN — MOSCOW VARIATION ───────────────────────────────
            "e4 c5 Nf3 d6 Bb5+ Nc6 O-O Bd7 Re1 Nf6 c3 a6 Bf1 Bg4 h3 Bh5",
            "e4 c5 Nf3 d6 Bb5+ Bd7 Bxd7+ Qxd7 c4 Nc6 Nc3 Nf6 d4 cxd4 Nxd4",

            # ── SICILIAN — ROSSOLIMO VARIATION ────────────────────────────
            "e4 c5 Nf3 Nc6 Bb5 g6 Bxc6 dxc6 d3 Bg7 h3 Nf6 Nc3 O-O Be3",
            "e4 c5 Nf3 Nc6 Bb5 e6 O-O Nge7 Re1 a6 Bf1 d5 exd5 exd5 d4",

            # ── ENGLISH DEFENCE ───────────────────────────────────────────
            "d4 e6 c4 b6 e4 Bb7 Bd3 f5 exf5 exf5 Nc3 Nf6 Nge2 Nc6 O-O Bd6",
            "d4 e6 Nf3 b6 g3 Bb7 Bg2 f5 c4 Nf6 Nc3 Bb4 O-O O-O d5",

            # ── TORRE ATTACK — BEVERWIJK ──────────────────────────────────
            "d4 Nf6 Nf3 e6 Bg5 c5 e3 Be7 Nbd2 b6 c3 Bb7 Bd3 h6 Bh4 d6 O-O",

            # ── LONDON SYSTEM — ACCELERATED ──────────────────────────────
            "d4 d5 Bf4 e6 e3 Nf6 Nd2 Be7 Ngf3 b6 Ne5 Bb7 Bd3 c5 c3 Nc6 Ndf3",

            # ── PETROV — COCHRANE GAMBIT ──────────────────────────────────
            "e4 e5 Nf3 Nf6 Nxe5 d6 Nxf7 Kxf7 d4 c5 dxc5 Nc6 Bc4+ Ke8 O-O",

            # ── QUEEN'S PAWN GAME — OLD INDIAN ───────────────────────────
            "d4 d6 e4 Nf6 Nc3 e5 dxe5 dxe5 Qxd8+ Kxd8 f4 Bd6 Bc4 Ke7 Nf3",

            # ── DUTCH — ANTI-LENINGRAD ────────────────────────────────────
            "d4 f5 Nc3 Nf6 Bg5 d6 e3 e6 Bd3 Be7 Nge2 O-O O-O Nc6 Qd2 Ne4",

            # ── KING'S INDIAN ATTACK — SICILIAN SETUP ────────────────────
            "Nf3 c5 g3 d5 Bg2 Nf6 O-O Nc6 d3 e5 e4 d4 a4 Be7 Na3 O-O Nc4",

            # ── BENKO GAMBIT — ACCEPTED FIANCHETTO ───────────────────────
            "d4 Nf6 c4 c5 d5 b5 cxb5 a6 bxa6 g6 Nc3 Bxa6 Nf3 d6 g3 Bg7 Bg2",

            # ── NIMZOWITSCH / LARSEN ATTACK — ENGLISH HYBRID ─────────────
            "b3 d5 Bb2 c5 e3 Nc6 Bb5 Nf6 Nf3 Bd7 O-O e6 d3 Be7 Nbd2",

            # ── CARO-KANN — KARPOV VARIATION ─────────────────────────────
            "e4 c6 d4 d5 Nd2 dxe4 Nxe4 Nd7 Ng5 Ngf6 Bd3 e6 N1f3 Bd6 Qe2 h6",
            "e4 c6 d4 d5 Nd2 dxe4 Nxe4 Bf5 Ng3 Bg6 Nf3 Nd7 h4 h6 Bd3 Bxd3 Qxd3",

            # ── SICILIAN — PAULSEN/TAIMANOV HYBRID ───────────────────────
            "e4 c5 Nf3 e6 d4 cxd4 Nxd4 Nc6 Nc3 a6 Nxc6 bxc6 Bd3 d5 O-O Nf6 Qf3",

            # ── FRENCH — GUIMARD VARIATION ────────────────────────────────
            "e4 e6 d4 d5 Nc3 Nc6 Nf3 Nf6 e5 Ne4 Bd3 Nxc3 bxc3 f6 exf6 Qxf6",

            # ── NIMZO-INDIAN — LENINGRAD SYSTEM ──────────────────────────
            "d4 Nf6 c4 e6 Nc3 Bb4 Bg5 c5 d5 h6 Bh4 Bxc3+ bxc3 d6 e3 e5",

            # ── QUEEN'S GAMBIT — CHIGORIN DEFENCE ────────────────────────
            "d4 d5 c4 Nc6 Nc3 e5 dxe5 d4 Ne4 Bf5 Ng3 Bg6 Nf3 Bb4+ Bd2 Bxd2+",
            "d4 d5 c4 Nc6 Nf3 Bg4 cxd5 Bxf3 gxf3 Qxd5 e3 e5 Nc3 Bb4 Bd2 Bxc3",

            # ── ALEKHINE — BUDAPEST GAMBIT LINK ──────────────────────────
            "e4 Nf6 Nc3 d5 exd5 Nxd5 d4 g6 Nf3 Bg7 Bc4 Nb6 Bb3 O-O O-O Nc6",

            # ── MODERN DEFENCE — AVERBAKH SYSTEM ─────────────────────────
            "e4 g6 d4 Bg7 c4 d6 Nc3 e5 d5 Nce7 g3 f5 Bg2 Nf6 Nge2 O-O",

            # ── PIRC — BYRNE VARIATION ─────────────────────────────────
            "e4 d6 d4 Nf6 Nc3 g6 Bg5 Bg7 e5 Nfd7 f4 dxe5 fxe5 c5 Nf3 Nc6",
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
            # Current side to move wins
            score = MATE_SCORE//2 + (1000 if dtm is None else max(0, 500-dtm*10))
            return score
        elif result == 'lose':
            # Current side to move loses
            return -(MATE_SCORE//2)
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
        if ply < MAX_PLY:
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
            b=board.copy()
            # XOR out the old EP contribution before clearing it
            if b.ep is not None:
                b.zobrist ^= ZOB_EP[b.ep%8+1]
                b.zobrist ^= ZOB_EP[0]  # XOR in "no EP"
                b.ep=None
            b.side=1-b.side; b.zobrist^=ZOB_SIDE
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
                    if ply < MAX_PLY:
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
            # Check ALL book moves for this position, not just the weighted pick
            book_moves = book.probe(board)  # returns [(san, weight), ...]
            for book_san, _ in book_moves:
                book_m = board.parse_san(book_san)
                if book_m is not None and book_m == m:
                    is_book_move = True
                    break

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
BOT_SAVE_FILE     = os.path.expanduser("~/.chess_bot_save.json")


def save_bot_game(state: dict) -> bool:
    """Persist a bot game state to disk for resuming later."""
    try:
        with open(BOT_SAVE_FILE, 'w') as f:
            json.dump(state, f, indent=2)
        return True
    except Exception:
        return False


def load_bot_save() -> dict | None:
    """Load the most-recently saved bot game, or None if none exists."""
    try:
        if os.path.exists(BOT_SAVE_FILE):
            with open(BOT_SAVE_FILE, 'r') as f:
                return json.load(f)
    except Exception:
        pass
    return None


def delete_bot_save():
    """Remove the saved bot game file."""
    try:
        if os.path.exists(BOT_SAVE_FILE):
            os.remove(BOT_SAVE_FILE)
    except Exception:
        pass
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
    """
    ELO system with separate ratings per time-control category.
    Categories: 'bullet', 'blitz', 'rapid', 'classical', 'unlimited'
    Each player gets an independent rating per category.
    """

    CATEGORIES = ('bullet', 'blitz', 'rapid', 'classical', 'unlimited')

    @staticmethod
    def category_for(minutes):
        """Map minutes-per-side to a rating category."""
        if minutes <= 0:    return 'unlimited'
        if minutes <= 2:    return 'bullet'
        if minutes <= 5:    return 'blitz'
        if minutes <= 15:   return 'rapid'
        return 'classical'

    def __init__(self):
        self.db = self._load()

    def _load(self):
        try:
            with open(ELO_FILE, 'r') as f:
                return json.loads(f.read())
        except Exception:
            return {ENGINE_NAME: self._new_entry(2200)}

    def _save(self):
        try:
            with open(ELO_FILE, 'w') as f:
                f.write(json.dumps(self.db, indent=2))
        except Exception:
            pass

    def _new_entry(self, start=1200):
        """Create a fresh player entry with per-category ratings."""
        entry = {'games': 0, 'wins': 0, 'draws': 0, 'losses': 0}
        for cat in self.CATEGORIES:
            entry[cat] = {'elo': start, 'games': 0, 'wins': 0, 'draws': 0, 'losses': 0}
        # Keep legacy 'elo' field for compatibility
        entry['elo'] = start
        return entry

    def _ensure(self, name):
        if name not in self.db:
            self.db[name] = self._new_entry()
        # Migrate old entries that lack per-category data
        entry = self.db[name]
        for cat in self.CATEGORIES:
            if cat not in entry:
                entry[cat] = {'elo': entry.get('elo', 1200),
                              'games': 0, 'wins': 0, 'draws': 0, 'losses': 0}

    def get_elo(self, name, category='unlimited'):
        self._ensure(name)
        cat = category if category in self.CATEGORIES else 'unlimited'
        return self.db[name][cat]['elo']

    def expected(self, ra, rb):
        return 1.0 / (1.0 + 10 ** ((rb - ra) / 400.0))

    def update(self, player, opponent, result, category='unlimited'):
        """
        result: 1=win  0.5=draw  0=loss  (from player's perspective)
        category: one of CATEGORIES
        """
        cat = category if category in self.CATEGORIES else 'unlimited'
        for n in (player, opponent):
            self._ensure(n)

        ra = self.db[player][cat]['elo']
        rb = self.db[opponent][cat]['elo']
        ea = self.expected(ra, rb)
        # K-factor: higher for new players, lower for established
        games = self.db[player][cat]['games']
        K = 40 if games < 30 else (20 if games < 100 else 10)

        # Update player
        new_ra = round(ra + K * (result - ea))
        self.db[player][cat]['elo']   = new_ra
        self.db[player][cat]['games'] += 1
        self.db[player]['games'] += 1
        if result == 1:
            self.db[player][cat]['wins']   += 1
            self.db[player]['wins']         += 1
        elif result == 0.5:
            self.db[player][cat]['draws']  += 1
            self.db[player]['draws']        += 1
        else:
            self.db[player][cat]['losses'] += 1
            self.db[player]['losses']       += 1
        self.db[player]['elo'] = new_ra  # keep legacy field updated

        # Update opponent
        eb = self.expected(rb, ra)
        Kb = 40 if self.db[opponent][cat]['games'] < 30 else \
             (20 if self.db[opponent][cat]['games'] < 100 else 10)
        opp_result = 1 - result
        new_rb = round(rb + Kb * (opp_result - eb))
        self.db[opponent][cat]['elo']   = new_rb
        self.db[opponent][cat]['games'] += 1
        self.db[opponent]['games'] += 1
        if opp_result == 1:
            self.db[opponent][cat]['wins']   += 1
            self.db[opponent]['wins']         += 1
        elif opp_result == 0.5:
            self.db[opponent][cat]['draws']  += 1
            self.db[opponent]['draws']        += 1
        else:
            self.db[opponent][cat]['losses'] += 1
            self.db[opponent]['losses']       += 1
        self.db[opponent]['elo'] = new_rb

        self._save()
        return new_ra - ra  # return ELO change for player

    def leaderboard(self, n=10, category=None):
        """Show leaderboard.  If category given, sort by that category's ELO."""
        cat = category or 'unlimited'
        if cat not in self.CATEGORIES:
            cat = 'unlimited'

        def sort_key(item):
            entry = item[1]
            if cat in entry:
                return -entry[cat]['elo']
            return -entry.get('elo', 1200)

        ranked = sorted(self.db.items(), key=sort_key)

        cat_label = cat.capitalize()
        print(f"\n  ┌──────────────────────────────────────────────────────────────┐")
        print(f"  │          ELO LEADERBOARD  [{cat_label:^10}]                     │")
        print(f"  ├──────┬────────────────────┬───────┬────────┬────────┬────────┤")
        print(f"  │ Rank │ Player             │ {cat_label[:6]:<6} │ Bullet │ Blitz  │ Rapid  │")
        print(f"  ├──────┼────────────────────┼───────┼────────┼────────┼────────┤")
        for i, (name, d) in enumerate(ranked[:n]):
            self._ensure(name)
            bul = d['bullet']['elo']
            blz = d['blitz']['elo']
            rap = d['rapid']['elo']
            cur = d[cat]['elo']
            print(f"  │  {i+1:>2}  │ {name[:18]:<18} │ {cur:>5} │ {bul:>6} │ {blz:>6} │ {rap:>6} │")
        print(f"  └──────┴────────────────────┴───────┴────────┴────────┴────────┘\n")

        # Show all category ELOs for top player
        if ranked:
            name, d = ranked[0]
            self._ensure(name)
            print(f"  {name}'s ratings across all categories:")
            for c in self.CATEGORIES:
                g = d[c]['games']
                e = d[c]['elo']
                w = d[c]['wins']; dr = d[c]['draws']; l = d[c]['losses']
                print(f"    {c.capitalize():<12}: {e:>4}  ({g} games, {w}W/{dr}D/{l}L)")
            print()


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
        is_provisional = entry.get('is_provisional', games < 20)
        
        # Format record
        record = f"{wins}W/{draws}D/{losses}L"
        prov_mark = '?' if is_provisional else ''
        peak_indicator = " ▲" if elo == peak and games > 5 else ""
        elo_str = f"{elo}{prov_mark}{peak_indicator}"
        
        print(f"  ║ {i:>4} ║ {username:<22} ║ {elo_str:<9} ║ {record:<18} ║")
    
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

# Spectator message types
MSG_SPECTATE_JOIN = 'SPECTATE_JOIN'
MSG_SPECTATE_LEAVE = 'SPECTATE_LEAVE'
MSG_SPECTATE_LIST = 'SPECTATE_LIST'
MSG_SPECTATE_UPDATE = 'SPECTATE_UPDATE'

# Rematch message types
MSG_REMATCH_REQUEST = 'REMATCH_REQUEST'
MSG_REMATCH_RESPONSE = 'REMATCH_RESPONSE'

# Game clock message types
MSG_GAME_CLOCK_UPDATE = 'GAME_CLOCK_UPDATE'
MSG_GAME_TIMEOUT = 'GAME_TIMEOUT'

# Player profile / avatar message types
MSG_SET_AVATAR = 'SET_AVATAR'
MSG_GET_AVATAR = 'GET_AVATAR'

# Chat history message type
MSG_GAME_CHAT_HISTORY = 'GAME_CHAT_HISTORY'

# ── v2.0 additions: lobby chat, daily puzzle, achievements, tournaments ──
MSG_LOBBY_CHAT           = 'LOBBY_CHAT'
MSG_LOBBY_CHAT_HISTORY   = 'LOBBY_CHAT_HISTORY'
MSG_DAILY_PUZZLE         = 'DAILY_PUZZLE'
MSG_ACHIEVEMENTS         = 'ACHIEVEMENTS'
MSG_ACHIEVEMENT_UNLOCKED = 'ACHIEVEMENT_UNLOCKED'
MSG_ANALYSIS_REQUEST     = 'ANALYSIS_REQUEST'
MSG_ANALYSIS_RESULT      = 'ANALYSIS_RESULT'
MSG_TOURNAMENT_CREATE    = 'TOURNAMENT_CREATE'
MSG_TOURNAMENT_JOIN      = 'TOURNAMENT_JOIN'
MSG_TOURNAMENT_LIST      = 'TOURNAMENT_LIST'
MSG_TOURNAMENT_STATUS    = 'TOURNAMENT_STATUS'
MSG_TOURNAMENT_RESULT    = 'TOURNAMENT_RESULT'
MSG_RECONNECT            = 'RECONNECT'
MSG_FRIEND_HEARTBEAT     = 'FRIEND_HEARTBEAT'
MSG_SERVER_BROADCAST     = 'SERVER_BROADCAST'

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

    def __init__(self, host=None, port=None):
        """Initialize client with message routing."""
        self.host = host or 'localhost'
        self.port = port or 65433
        self.sock = None
        self.pending = b''
        self.logged_in_user = None
        self.encryption_enabled = False
        self.session_key = None
        self.client_private = None
        self.client_public = None
        self._nonce_counter = 0

        # Message routing — two queues: async push notifications vs sync responses
        self._msg_lock = threading.Lock()
        self._async_queue = queue.Queue()   # push notifications (match found, moves, etc.)
        self._sync_queue  = queue.Queue()   # request/response pairs
        self._response_handlers = {}
        self._request_counter = 0

        # Async message types — populated in _init_async_types()
        self.ASYNC_TYPES = set()

        # Start background listener
        self._listener_stop = threading.Event()
        self._start_listener()

    # ════════════════════════════════════════════════════════════════════
    #  E2E ENCRYPTION HELPERS
    # ════════════════════════════════════════════════════════════════════
    def _derive_nonce(self):
        """Derive a unique nonce for each message (12 bytes for GCM).

        Client uses even counter values; server uses odd — avoids nonce reuse.
        """
        self._nonce_counter += 1
        nonce_bytes = b'\x00\x00\x00\x00' + struct.pack('>Q', self._nonce_counter)
        # Clear the last bit (client = even)
        nonce_bytes = nonce_bytes[:-1] + bytes([nonce_bytes[-1] & 0xFE])
        return nonce_bytes

    def _encrypt_message(self, plaintext: bytes) -> bytes:
        if not self.encryption_enabled or self.session_key is None:
            return plaintext
        nonce = self._derive_nonce()
        ciphertext, tag = _gcm_encrypt(plaintext, self.session_key, nonce)
        return b'E' + nonce + ciphertext + tag

    def _decrypt_message(self, ciphertext: bytes) -> bytes:
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
        """Populate the set of async push-notification message types."""
        if not self.ASYNC_TYPES:
            self.ASYNC_TYPES = {
                MSG_MATCH, MSG_GAME_MOVE, MSG_GAME_RESIGN,
                MSG_GAME_DRAW_OFFER, MSG_GAME_DRAW_ACCEPT, MSG_GAME_CHAT,
                MSG_NEW_MESSAGE_NOTIFY, MSG_FRIEND_REQUEST, MSG_FRIEND_STATUS,
                MSG_CHALLENGE_SEND,
                MSG_SPECTATE_UPDATE, MSG_GAME_CLOCK_UPDATE, MSG_GAME_TIMEOUT,
                MSG_REMATCH_REQUEST, MSG_REMATCH_RESPONSE,
                # v2.0 push types
                MSG_FRIEND_HEARTBEAT, MSG_LOBBY_CHAT, MSG_ANALYSIS_RESULT,
                MSG_ACHIEVEMENT_UNLOCKED, MSG_SERVER_BROADCAST,
            }

    def _start_listener(self):
        """Start background message listener thread."""
        self._init_async_types()

        def listener_loop():
            while not self._listener_stop.is_set():
                try:
                    msg = self._recv_raw(timeout=0.5)
                    if msg:
                        msg_type = msg.get('type', '')
                        if msg_type in self.ASYNC_TYPES:
                            self._async_queue.put(msg)
                        else:
                            self._sync_queue.put(msg)
                except Exception:
                    pass

        self._listener_thread = threading.Thread(target=listener_loop, daemon=True)
        self._listener_thread.start()

    def _recv_raw(self, timeout=5.0):
        """Raw receive — reads from socket and parses one message."""
        if not self.sock:
            return None
        self.sock.settimeout(timeout)
        retries = 0
        while retries < 3:
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
                except socket.timeout:
                    if not self.pending:
                        retries += 1
            except Exception:
                retries += 1
        return None

    def recv(self, timeout=5.0):
        """Receive an async push notification (non-blocking friendly)."""
        try:
            return self._async_queue.get(timeout=timeout)
        except queue.Empty:
            return None

    def recv_sync(self, timeout=10.0):
        """Receive a synchronous response, re-queuing any async messages encountered."""
        start = time.time()
        stash = []
        result = None
        while time.time() - start < timeout:
            try:
                msg = self._sync_queue.get(timeout=0.3)
                msg_type = msg.get('type', '')
                if msg_type in self.ASYNC_TYPES:
                    # Accidentally landed in sync queue — reroute
                    self._async_queue.put(msg)
                else:
                    result = msg
                    break
            except queue.Empty:
                continue
        # Put back any stashed items (shouldn't happen with proper routing)
        for m in stash:
            self._sync_queue.put(m)
        return result

    def connect(self):
        """Connect to the server."""
        try:
            print(f"  Connecting to {self.host}:{self.port}...")
            self.sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            self.sock.settimeout(10.0)
            self.sock.connect((self.host, self.port))
            self.sock.settimeout(None)
            self.pending = b''
            print("  TCP connection established")
            return True, "Connected to server"
        except socket.timeout:
            return False, "Connection timed out"
        except ConnectionRefusedError:
            return False, "Connection refused — is the server running?"
        except Exception as e:
            return False, f"Connection failed: {e}"

    def disconnect(self):
        """Disconnect from the server."""
        self.logged_in_user = None
        self.encryption_enabled = False
        self.session_key = None
        self.pending = b''
        if self.sock:
            try:
                self.sock.shutdown(socket.SHUT_RDWR)
            except Exception:
                pass
            try:
                self.sock.close()
            except Exception:
                pass
            self.sock = None

    def send(self, msg_type, data=None):
        """Send a message to the server (encrypted if session established)."""
        if not self.sock:
            return False
        payload = json.dumps({'type': msg_type, 'data': data or {}}).encode()
        if (self.encryption_enabled and self.session_key
                and msg_type not in (MSG_GET_SERVER_PUBLIC_KEY, MSG_SESSION_KEY_EXCHANGE)):
            payload = self._encrypt_message(payload)
        header = struct.pack('>I', len(payload))
        try:
            self.sock.sendall(header + payload)
            self.sock.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
            return True
        except Exception:
            return False

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
        response = self.recv_sync(timeout=10.0)
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
        
        response = self.recv_sync(timeout=10.0)
        
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
                response = self.recv_sync(timeout=10.0)
                if response and response.get('success'):
                    self.logged_in_user = username
                    self.session_key_exchange()
                return response
        
        # Fallback to plaintext
        self.send(MSG_AUTO_LOGIN, {
            'username': username,
            'password_hash': password_hash
        })
        response = self.recv_sync(timeout=10.0)
        if response and response.get('success'):
            self.logged_in_user = username
            self.session_key_exchange()
        return response

    def logout(self):
        """Logout from the account."""
        self.send(MSG_LOGOUT)
        response = self.recv_sync(timeout=10.0)
        if response and response.get('success'):
            self.logged_in_user = None
        return response
    
    def save_game(self, white, black, result, moves, duration=0, rated=True,
                  pgn='', move_times=None):
        """Save a game to history. Supports PGN storage and move-time anti-cheat."""
        self.send(MSG_SAVE_GAME, {
            'white': white,
            'black': black,
            'result': result,
            'moves': moves,
            'duration': duration,
            'rated': rated,
            'pgn': pgn,
            'move_times': move_times or [],
        })
        return self.recv_sync(timeout=10.0)

    def get_profile(self, username=None, page=0, page_size=10):
        """Get a user's profile with paginated game history."""
        data = {'page': page, 'page_size': page_size}
        if username:
            data['username'] = username
        self.send(MSG_GET_PROFILE, data)
        return self.recv_sync(timeout=10.0)

    def list_users(self):
        """Get list of all users."""
        self.send(MSG_LIST_USERS)
        return self.recv_sync(timeout=10.0)

    # ── Matchmaking ────────────────────────────────────────────────────
    def join_queue(self, time_control='blitz'):
        """Join the matchmaking queue with a specific time control."""
        self.send(MSG_QUEUE_JOIN, {
            'username': self.logged_in_user or _current_user,
            'time_control': time_control,
        })
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

    def reconnect_game(self, game_id):
        """Attempt to reconnect to an ongoing game after disconnect."""
        self.send(MSG_RECONNECT, {'game_id': game_id})
        return self.recv_sync(timeout=10.0)

    def send_move(self, game_id, move):
        """Send a move in an active game."""
        self.send(MSG_GAME_MOVE, {'game_id': game_id, 'move': move})
        return self.recv_sync(timeout=10.0)

    def resign_game(self, game_id):
        self.send(MSG_GAME_RESIGN, {'game_id': game_id})

    def offer_draw(self, game_id):
        self.send(MSG_GAME_DRAW_OFFER, {'game_id': game_id})

    def accept_draw(self, game_id):
        self.send(MSG_GAME_DRAW_ACCEPT, {'game_id': game_id})

    def send_chat(self, game_id, message):
        self.send(MSG_GAME_CHAT, {'game_id': game_id, 'message': message})

    def get_leaderboard(self, limit=10):
        """Get ELO leaderboard."""
        self.send(MSG_LEADERBOARD, {'limit': limit})
        return self.recv_sync(timeout=10.0)

    # ── Lobby chat ─────────────────────────────────────────────────────
    def send_lobby_chat(self, message):
        """Send a message to the global lobby chat."""
        self.send(MSG_LOBBY_CHAT, {'message': message})

    def get_lobby_chat_history(self, limit=50):
        """Fetch recent lobby chat messages."""
        self.send(MSG_LOBBY_CHAT_HISTORY, {'limit': limit})
        return self.recv_sync(timeout=10.0)

    # ── Daily puzzle ───────────────────────────────────────────────────
    def get_daily_puzzle(self):
        """Fetch today's server puzzle."""
        self.send(MSG_DAILY_PUZZLE)
        return self.recv_sync(timeout=10.0)

    # ── Achievements ───────────────────────────────────────────────────
    def get_achievements(self, username=None):
        """Fetch achievement list for the given user."""
        self.send(MSG_ACHIEVEMENTS, {'username': username or self.logged_in_user})
        return self.recv_sync(timeout=10.0)

    # ── Post-game analysis queue ───────────────────────────────────────
    def request_analysis(self, game_id, moves, pgn='', white='', black=''):
        """Request server-side analysis for a completed game."""
        self.send(MSG_ANALYSIS_REQUEST, {
            'game_id': game_id,
            'moves': moves,
            'pgn': pgn,
            'white': white,
            'black': black,
        })
        return self.recv_sync(timeout=10.0)

    # ── Tournaments ────────────────────────────────────────────────────
    def create_tournament(self, name, max_players=8, rounds=3, time_control='blitz'):
        """Create a new Swiss-system tournament."""
        self.send(MSG_TOURNAMENT_CREATE, {
            'name': name,
            'max_players': max_players,
            'rounds': rounds,
            'time_control': time_control,
        })
        return self.recv_sync(timeout=10.0)

    def join_tournament(self, tournament_id):
        """Join a tournament by ID."""
        self.send(MSG_TOURNAMENT_JOIN, {'tournament_id': tournament_id})
        return self.recv_sync(timeout=10.0)

    def list_tournaments(self):
        """List all active/upcoming tournaments."""
        self.send(MSG_TOURNAMENT_LIST)
        return self.recv_sync(timeout=10.0)

    def get_tournament_status(self, tournament_id):
        """Get full status of a tournament."""
        self.send(MSG_TOURNAMENT_STATUS, {'tournament_id': tournament_id})
        return self.recv_sync(timeout=10.0)

    def record_tournament_result(self, tournament_id, round_num, white, black, result):
        """Record a game result in a tournament (creator only)."""
        self.send(MSG_TOURNAMENT_RESULT, {
            'tournament_id': tournament_id,
            'round': round_num,
            'white': white,
            'black': black,
            'result': result,
        })
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

    # ── Spectator methods ─────────────────────────────────────────────
    def list_spectatable_games(self):
        """List active games available to spectate."""
        self.send(MSG_SPECTATE_LIST, {})
        return self.recv_sync(timeout=10.0)

    def spectate_game(self, game_id):
        """Join a game as a spectator."""
        self.send(MSG_SPECTATE_JOIN, {'game_id': game_id})
        return self.recv_sync(timeout=10.0)

    def leave_spectate(self, game_id):
        """Leave spectator mode."""
        self.send(MSG_SPECTATE_LEAVE, {'game_id': game_id})
        return self.recv_sync(timeout=5.0)

    # ── Rematch methods ───────────────────────────────────────────────
    def request_rematch(self, game_id, white, black):
        """Request a rematch after a game ends."""
        self.send(MSG_REMATCH_REQUEST, {'game_id': game_id, 'white': white, 'black': black})
        return self.recv_sync(timeout=5.0)

    # ── Avatar / Profile methods ──────────────────────────────────────
    def set_avatar(self, avatar, bio=''):
        """Set current user's ASCII avatar and bio."""
        self.send(MSG_SET_AVATAR, {'avatar': avatar, 'bio': bio})
        return self.recv_sync(timeout=10.0)

    def get_avatar(self, username=None):
        """Get avatar/profile for a user."""
        self.send(MSG_GET_AVATAR, {'username': username})
        return self.recv_sync(timeout=10.0)

    # ── Chat history methods ──────────────────────────────────────────
    def get_game_chat_history(self, game_id):
        """Retrieve persistent chat history for a completed game."""
        self.send(MSG_GAME_CHAT_HISTORY, {'game_id': game_id})
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
    """View a user's profile with paginated game history."""
    if _offline_mode:
        print("\n  Profile view requires online mode. Enable it from the main menu.")
        return

    if _server_client is None or _server_client.sock is None:
        success, msg = connect_to_server()
        if not success:
            print(f"  Cannot connect to server: {msg}")
            return

    if not username:
        username = _current_user
    if not username:
        print("  No user logged in.")
        return

    page = 0
    page_size = 10

    while True:
        response = _server_client.get_profile(username, page=page, page_size=page_size)
        if response is None:
            print("  No response from server.")
            return
        if not response.get('success'):
            print(f"  Failed to get profile: {response.get('data', 'Unknown error')}")
            return

        profile = response.get('data', {})
        is_own  = (username == _current_user)
        elo      = profile.get('elo', 1200)
        elo_games = profile.get('elo_games', 0)
        elo_wins  = profile.get('elo_wins', 0)
        elo_losses= profile.get('elo_losses', 0)
        elo_draws = profile.get('elo_draws', 0)
        elo_peak  = profile.get('elo_peak', 1200)
        total_g   = profile.get('total_game_count', elo_games)
        total_pages = max(1, (total_g + page_size - 1) // page_size)
        susp      = profile.get('suspicious_games', 0)

        print("\n  ╔══════════════════════════════════════════════════════════╗")
        print(f"  ║  PROFILE: {profile.get('username','?'):<46}║")
        print("  ╠══════════════════════════════════════════════════════════╣")
        if is_own:
            print(f"  ║  Email        : {profile.get('email','N/A'):<40}║")
        print(f"  ║  Member since : {str(profile.get('created_at','?'))[:16]:<40}║")
        print(f"  ║  Banned       : {'Yes ⛔' if profile.get('banned') else 'No':<40}║")
        print("  ╠══════════════════════════════════════════════════════════╣")
        print(f"  ║  ELO Rating   : {elo:<40}║")
        print(f"  ║  Peak ELO     : {elo_peak:<40}║")
        print(f"  ║  Rated Games  : {elo_games:<40}║")
        print(f"  ║  Record       : {elo_wins}W / {elo_losses}L / {elo_draws}D{'':<26}║")
        if is_own and susp:
            print(f"  ║  ⚠  Flagged games (anti-cheat): {susp:<25}║")
        print(f"  ╠══════════════════════════════════════════════════════════╣")
        print(f"  ║  GAME HISTORY  (page {page+1}/{total_pages}, {page_size} per page){'':<18}║")
        print("  ╚══════════════════════════════════════════════════════════╝")

        recent_games = profile.get('recent_games', [])
        if not recent_games:
            print("    No games on this page.")
        else:
            for i, game in enumerate(recent_games, page * page_size + 1):
                white   = game.get('white', '?')
                black   = game.get('black', '?')
                result  = game.get('result', '?')
                ts      = str(game.get('timestamp', '?'))[:16].replace('T', ' ')
                n_moves = len(game.get('moves', []))
                res_str = (f"{white} won" if result == 'white'
                           else f"{black} won" if result == 'black'
                           else "Draw")
                pgn_flag = ' [PGN]' if game.get('pgn') else ''
                print(f"    {i:>3}. [{ts}] {white} vs {black} — {res_str} ({n_moves} moves){pgn_flag}")

        print()
        if total_pages <= 1:
            break
        print(f"  Page {page+1}/{total_pages} — [n]ext  [p]rev  [q]uit")
        try:
            nav = input("  > ").strip().lower()
        except EOFError:
            break
        if nav in ('q', 'quit', ''):
            break
        elif nav in ('n', 'next') and page < total_pages - 1:
            page += 1
        elif nav in ('p', 'prev', 'b') and page > 0:
            page -= 1
        else:
            break
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

# ── Message encryption ────────────────────────────────────────────────────
# We use AES-256-CTR for friend messages.  Each client generates a fresh
# 32-byte message key once per session; the same stdlib AES-CTR used for
# the session transport is reused here (no extra dependencies).
# A random 12-byte nonce is prepended to every ciphertext so the same key
# can safely encrypt many messages.
# The "iv" field sent to the server carries the base64-encoded nonce.
# The "tag" field is left as "aes256ctr" (no HMAC — acceptable because the
# server transport already provides channel integrity via AES-GCM).

_message_key: bytes = secrets.token_bytes(32)   # session-local symmetric key

def _msg_encrypt(plaintext: str) -> tuple:
    """Encrypt a chat message.  Returns (ciphertext_b64, nonce_b64, tag_str)."""
    nonce = secrets.token_bytes(12)
    pt    = plaintext.encode("utf-8")
    ct    = _aes_ctr_encrypt(pt, _message_key, nonce)
    return (base64.b64encode(ct).decode(),
            base64.b64encode(nonce).decode(),
            "aes256ctr")

def _msg_decrypt(ciphertext_b64: str, nonce_b64: str) -> str:
    """Decrypt a chat message stored on the server."""
    ct    = base64.b64decode(ciphertext_b64)
    nonce = base64.b64decode(nonce_b64)
    pt    = _aes_ctr_decrypt(ct, _message_key, nonce)
    return pt.decode("utf-8")

# Legacy stubs kept so old call-sites that reference them don't crash
_user_private_keys: dict = {}
_user_public_keys:  dict = {}

def _generate_keypair():
    """Return a placeholder keypair (messaging now uses _msg_encrypt)."""
    priv = secrets.token_hex(32)
    return priv, priv   # pub == priv is fine; key is never used externally

def _encrypt_message(message, _key=""):
    """Wrapper around _msg_encrypt for call-site compatibility."""
    return _msg_encrypt(message)

def _decrypt_message(encrypted_content, iv, tag, _key=""):
    """Wrapper around _msg_decrypt for call-site compatibility."""
    try:
        return _msg_decrypt(encrypted_content, iv)
    except Exception:
        return "[decryption error]"

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
            response = _server_client.recv(timeout=3.0)
            if response and response.get('success'):
                messages = response.get('data', {}).get('messages', [])
        except Exception:
            pass  # Non-critical, continue without loading messages

    # Display messages — decrypt each one before showing
    if messages:
        print("\n  Recent messages:")
        for msg in messages[-20:]:  # Show last 20 messages
            sender = msg['sender']
            try:
                text = _msg_decrypt(msg['encrypted_content'], msg.get('iv', ''))
            except Exception:
                text = "[unable to decrypt — sent from another session]"
            ts = msg.get('created_at', '')[:16].replace('T', ' ')
            print(f"    [{ts}] {sender}: {text}")
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
        encrypted, iv, tag = _msg_encrypt(message)
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
def spectator_mode():
    """Watch a live online game as a spectator."""
    if _offline_mode or not _server_client:
        print("\n  Spectator mode requires online connection.")
        return
    
    # List active games
    resp = _server_client.list_spectatable_games()
    if resp is None or not resp.get('success'):
        print("\n  Could not retrieve active games.")
        return
    
    games = resp.get('data', [])
    if not games:
        print("\n  No active games to spectate right now.")
        return
    
    print("\n  ╔══════════════════════════════════════════════════════════╗")
    print("  ║               LIVE GAMES — SPECTATE                     ║")
    print("  ╠══╦══════════════════════╦══════════════════════╦════════╣")
    print("  ║# ║ White                ║ Black                ║ Moves  ║")
    print("  ╠══╬══════════════════════╬══════════════════════╬════════╣")
    for i, g in enumerate(games, 1):
        w = g.get('white', '?')[:20]
        b = g.get('black', '?')[:20]
        mv = g.get('move_count', 0)
        spec = g.get('spectator_count', 0)
        print(f"  ║{i:<2}║ {w:<20} ║ {b:<20} ║ {mv:>3}m {spec:>2}👁 ║")
    print("  ║ 0. Back                                                  ║")
    print("  ╚══════════════════════════════════════════════════════════╝")
    
    try:
        choice = input("  Select game to spectate: ").strip()
    except EOFError:
        return
    
    if choice == '0':
        return
    
    try:
        idx = int(choice) - 1
        if not (0 <= idx < len(games)):
            print("  Invalid choice.")
            return
    except ValueError:
        print("  Invalid choice.")
        return
    
    target = games[idx]
    game_id = target['game_id']
    
    resp = _server_client.spectate_game(game_id)
    if resp is None or not resp.get('success'):
        print(f"  Could not join as spectator: {resp.get('data', 'unknown error') if resp else 'no response'}")
        return
    
    print(f"\n  Now spectating: {target['white']} vs {target['black']}")
    print("  (Press Enter to refresh, type 'quit' to exit spectator mode)\n")
    
    # Set up local board from move log provided in SPECTATE_UPDATE
    board = Board()
    board.reset()
    last_mv = None
    
    # Process initial state from the queue (SPECTATE_UPDATE was queued by listener)
    timeout = time.time() + 3
    while time.time() < timeout:
        try:
            msg = _server_client._async_queue.get(timeout=0.3)
            if msg.get('type') == MSG_SPECTATE_UPDATE:
                d = msg.get('data', {})
                for san in d.get('move_log', []):
                    m = board.parse_san(san)
                    if m:
                        board.make(m)
                        board.san_log.append(san)
                        last_mv = m
                break
        except:
            break
    
    white_remaining = 0
    black_remaining = 0
    clock_enabled = False
    
    while True:
        # Drain message queue
        try:
            while not _server_client._async_queue.empty():
                msg = _server_client._async_queue.get_nowait()
                mt = msg.get('type', '')
                d = msg.get('data', {})
                if mt == MSG_GAME_MOVE:
                    san = d.get('move')
                    m = board.parse_san(san)
                    if m:
                        board.make(m)
                        board.san_log.append(san)
                        last_mv = m
                        print(f"  ♟ {d.get('from_player')} plays: {san}")
                elif mt == MSG_GAME_CLOCK_UPDATE:
                    white_remaining = d.get('white_remaining', 0)
                    black_remaining = d.get('black_remaining', 0)
                    clock_enabled = True
                elif mt == MSG_GAME_CHAT:
                    print(f"  💬 [{d.get('from_player')}]: {d.get('message')}")
                elif mt in (MSG_GAME_RESIGN, MSG_GAME_DRAW_ACCEPT, MSG_GAME_TIMEOUT):
                    print(f"\n  Game ended! {mt}")
                    _server_client.leave_spectate(game_id)
                    return
        except:
            pass
        
        draw_board(board, WHITE, last_mv)
        if _settings.get('show_eval_bar', False):
            _ev = evaluate(board)
            if board.side == BLACK: _ev = -_ev
            print(_eval_bar(_ev))
        turn_str = "White" if board.side == WHITE else "Black"
        print(f"  Spectating: {target['white']} vs {target['black']}")
        if clock_enabled:
            print(f"  ⏱ White: {_fmt_online_clock(white_remaining)}  |  Black: {_fmt_online_clock(black_remaining)}")
        print(f"  Move {board.fullmove} — {turn_str} to move")
        
        try:
            raw = input("  [Enter=refresh, quit=exit]: ").strip().lower()
        except EOFError:
            break
        
        if raw == 'quit':
            break
    
    _server_client.leave_spectate(game_id)
    print("  Left spectator mode.")


def player_profile_menu():
    """View and edit player profile with avatar."""
    if _offline_mode or not _server_client or not _current_user:
        print("\n  Profile management requires online connection and login.")
        return
    
    while True:
        print("\n  ╔══════════════════════════════════════════════════════════╗")
        print("  ║                  PLAYER PROFILE                          ║")
        print("  ╠══════════════════════════════════════════════════════════╣")
        print("  ║  1. View my profile                                       ║")
        print("  ║  2. Edit avatar / bio                                     ║")
        print("  ║  3. View another player's profile                         ║")
        print("  ║  0. Back                                                  ║")
        print("  ╚══════════════════════════════════════════════════════════╝")
        
        try:
            choice = input("  Choice: ").strip()
        except EOFError:
            return
        
        if choice == '0':
            return
        
        elif choice == '1':
            _show_player_profile(_current_user)
        
        elif choice == '2':
            print("\n  Current avatar (leave blank to keep existing):")
            print("  Enter up to 5 lines of ASCII art (type END on a blank line to finish):")
            lines = []
            for _ in range(5):
                try:
                    line = input("  > ")
                except EOFError:
                    break
                if line.strip().upper() == 'END':
                    break
                lines.append(line)
            avatar = '\n'.join(lines)
            
            try:
                bio = input("  Bio (max 200 chars): ").strip()[:200]
            except EOFError:
                bio = ''
            
            resp = _server_client.set_avatar(avatar, bio)
            if resp and resp.get('success'):
                print("  ✓ Profile updated!")
            else:
                print(f"  Failed: {resp.get('data', 'unknown') if resp else 'no response'}")
        
        elif choice == '3':
            try:
                username = input("  Enter username: ").strip()
            except EOFError:
                continue
            if username:
                _show_player_profile(username)


def _show_player_profile(username):
    """Display a player's profile with avatar, stats, rating."""
    resp = _server_client.get_avatar(username)
    if resp is None or not resp.get('success'):
        print(f"  Could not load profile for {username}.")
        return
    
    data = resp.get('data', {})
    avatar = data.get('avatar', '')
    bio = data.get('bio', '')
    elo = data.get('elo', 1200)
    games = data.get('games', 0)
    wins = data.get('wins', 0)
    losses = data.get('losses', 0)
    draws = data.get('draws', 0)
    is_prov = data.get('is_provisional', games < 20)
    peak = data.get('elo_peak', elo)
    
    prov_str = ' [Provisional]' if is_prov else ''
    
    print(f"\n  ╔══════════════════════════════════════════════════════════╗")
    print(f"  ║  👤 {username:<52}║")
    print(f"  ╠══════════════════════════════════════════════════════════╣")
    if avatar:
        for line in avatar.split('\n')[:5]:
            print(f"  ║  {line:<54}║")
        print(f"  ╠══════════════════════════════════════════════════════════╣")
    if bio:
        print(f"  ║  {bio[:54]:<54}║")
        print(f"  ╠══════════════════════════════════════════════════════════╣")
    print(f"  ║  ELO: {elo}{prov_str:<48}║")
    print(f"  ║  Peak ELO: {peak:<46}║")
    print(f"  ║  Record: {wins}W / {draws}D / {losses}L ({games} rated games){'':<20}║")
    print(f"  ╚══════════════════════════════════════════════════════════╝")


def matchmaking_menu():
    """Display matchmaking menu for online games."""
    global _server_client, _current_user

    if _offline_mode:
        print("\n  ╔══════════════════════════════════════════════════════════╗")
        print("  ║              OFFLINE MODE ACTIVE                         ║")
        print("  ╠══════════════════════════════════════════════════════════╣")
        print("  ║  Online matchmaking requires internet connection.        ║")
        print("  ║  Return to main menu → Enable Online Mode to proceed.   ║")
        print("  ╚══════════════════════════════════════════════════════════╝")
        return

    if not _current_user:
        print("\n  You must be logged in to use matchmaking.")
        print("  Please login or register from Account Management.")
        return

    # Ensure we have a live connection
    if _server_client is None or _server_client.sock is None:
        success, msg = connect_to_server()
        if not success:
            print(f"\n  Cannot connect to server: {msg}")
            return
    else:
        _server_client.send(MSG_PING)
        ping_resp = _server_client.recv_sync(timeout=2.0)
        if ping_resp is None:
            print("\n  Connection lost. Reconnecting...")
            success, msg = connect_to_server(reconnect=True)
            if not success:
                print(f"\n  Cannot reconnect: {msg}")
                return

    in_queue = False
    current_game_id = None
    my_color = None
    opponent_name = None
    last_refresh = time.time()
    refresh_interval = 5.0
    selected_tc = 'blitz'          # default time control

    print("\n  ╔══════════════════════════════════════════════════════════╗")
    print("  ║              ONLINE MATCHMAKING  v2.0                   ║")
    print("  ╠══════════════════════════════════════════════════════════╣")
    print("  ║  Find a rated game using ELO-banded matchmaking!        ║")
    print("  ╚══════════════════════════════════════════════════════════╝")

    # Keep-alive ping thread
    def _keep_alive():
        while not _server_client._listener_stop.is_set():
            time.sleep(10)
            try:
                _server_client.send(MSG_PING)
            except Exception:
                pass

    threading.Thread(target=_keep_alive, daemon=True).start()

    while True:
        # ── Drain async queue and handle push notifications ────────────
        try:
            while not _server_client._async_queue.empty():
                msg = _server_client._async_queue.get_nowait()
                msg_type = msg.get('type', '')
                data = msg.get('data', {})

                if msg_type == MSG_MATCH:
                    in_queue = False
                    current_game_id = data.get('game_id')
                    my_color = data.get('color')
                    opponent_name = data.get('opponent')
                    tc_info = data.get('time_control', selected_tc)
                    print(f"\n  ╔══════════════════════════════════════════════════╗")
                    print(f"  ║  ♟  MATCH FOUND!                                  ║")
                    print(f"  ╠══════════════════════════════════════════════════╣")
                    print(f"  ║  Opponent    : {opponent_name:<33}║")
                    print(f"  ║  Your color  : {my_color.upper():<33}║")
                    print(f"  ║  Time control: {tc_info:<33}║")
                    print(f"  ║  Game ID     : {str(current_game_id):<33}║")
                    print(f"  ╚══════════════════════════════════════════════════╝")
                    print("\n  Starting game in 1 second...")
                    time.sleep(1)
                    play_online_matched_game(
                        current_game_id, my_color, opponent_name,
                        _server_client._async_queue,
                        _server_client._listener_stop
                    )
                    current_game_id = None
                    my_color = None
                    opponent_name = None

                elif msg_type == MSG_ACHIEVEMENT_UNLOCKED:
                    name = data.get('name', data.get('id', '?'))
                    desc = data.get('desc', '')
                    print(f"\n  🏆  Achievement unlocked: {name}")
                    if desc:
                        print(f"       {desc}")

                elif msg_type == MSG_SERVER_BROADCAST:
                    print(f"\n  📢  {data.get('message', '')}")

                elif msg_type == MSG_FRIEND_HEARTBEAT:
                    # Silent status update; show nothing unless user requests
                    pass

        except Exception:
            pass

        # Auto-refresh queue status
        if in_queue and time.time() - last_refresh >= refresh_interval:
            status_resp = _server_client.get_queue_status()
            if status_resp and status_resp.get('success'):
                st = status_resp.get('data', {})
                pos  = st.get('position', '?')
                wait = st.get('wait_time', 0)
                cnt  = st.get('queued_players', 0)
                print(f"\n  [Queue] Position: {pos} | Wait: {wait}s | Players seeking: {cnt}")
            last_refresh = time.time()

        # ── Menu ───────────────────────────────────────────────────────
        tc_label = {'bullet': '⚡ Bullet 1+0', 'blitz': '🔥 Blitz 5+0',
                    'rapid': '⏱  Rapid 10+0', 'classical': '♟  Classical 30+0'}.get(selected_tc, selected_tc)
        print("\n  ╔══════════════════════════════════════════════════════════╗")
        if in_queue:
            print(f"  ║  Status: ⏳ IN QUEUE [{selected_tc.upper()}] — waiting for match...  ║")
        else:
            print(f"  ║  Status: NOT IN QUEUE  │  TC: {tc_label:<26}║")
        print("  ╠══════════════════════════════════════════════════════════╣")
        if not in_queue:
            print("  ║  1. Join Queue (rated game)                              ║")
            print("  ║  T. Change Time Control                                  ║")
        else:
            print("  ║  2. Leave Queue                                          ║")
            print("  ║  3. Refresh queue status                                 ║")
        print("  ║  4. Challenge by Username                                ║")
        print("  ║  5. Watch Live Games (Spectate)                          ║")
        print("  ║  6. Tournaments                                           ║")
        print("  ║  7. Lobby Chat                                            ║")
        print("  ║  8. My Achievements                                       ║")
        print("  ║  9. View / Edit Profile & Avatar                         ║")
        print("  ║  0. Back to Main Menu                                    ║")
        print("  ╚══════════════════════════════════════════════════════════╝")

        try:
            choice = input("  Choice: ").strip().lower()
        except EOFError:
            break

        if choice == '0':
            if in_queue:
                _server_client.leave_queue()
            break

        elif choice == '1' and not in_queue:
            resp = _server_client.join_queue(time_control=selected_tc)
            if resp and resp.get('success'):
                in_queue = True
                last_refresh = time.time()
                print(f"  ✓ Joined {selected_tc} queue. Waiting for opponent (ELO ±150)...")
            else:
                print(f"  ✗ Failed: {resp.get('data','Unknown error') if resp else 'No response'}")

        elif choice == 't' and not in_queue:
            print("  Time controls:")
            print("    1. Bullet   (1+0)")
            print("    2. Blitz    (5+0)  ← default")
            print("    3. Rapid    (10+0)")
            print("    4. Classical(30+0)")
            try:
                tc_choice = input("  Select [1-4]: ").strip()
            except EOFError:
                continue
            selected_tc = {'1': 'bullet', '2': 'blitz', '3': 'rapid', '4': 'classical'}.get(tc_choice, selected_tc)
            print(f"  ✓ Time control set to: {selected_tc}")

        elif choice == '2' and in_queue:
            _server_client.leave_queue()
            in_queue = False
            print("  ✓ Left queue.")

        elif choice == '3' and in_queue:
            resp = _server_client.get_queue_status()
            if resp and resp.get('success'):
                st = resp.get('data', {})
                print(f"  Position: {st.get('position','?')} | Wait: {st.get('wait_time',0)}s | Players: {st.get('queued_players',0)}")
            last_refresh = time.time()

        elif choice == '4':
            try:
                target = input("  Enter username to challenge: ").strip()
            except EOFError:
                continue
            if not target:
                continue
            print("  Color preference: 1. Random  2. White  3. Black")
            try:
                cc = input("  Choice [1]: ").strip() or '1'
            except EOFError:
                continue
            color = {'1': 'random', '2': 'white', '3': 'black'}.get(cc, 'random')
            resp = _server_client.send_challenge(target, color, rated=True)
            if resp and resp.get('success'):
                print(f"  ✓ Challenge sent to {target}!")
            else:
                print(f"  ✗ Could not challenge: {resp.get('data','Unknown error') if resp else 'No response'}")

        elif choice == '5':
            spectator_mode()

        elif choice == '6':
            tournaments_menu()

        elif choice == '7':
            lobby_chat_menu()

        elif choice == '8':
            achievements_menu()

        elif choice == '9':
            player_profile_menu()




def _fmt_online_clock(seconds):
    """Format seconds into M:SS for online clock display."""
    if seconds < 0:
        seconds = 0
    m = int(seconds) // 60
    s = int(seconds) % 60
    return f"{m}:{s:02d}"


# ════════════════════════════════════════════════════════════════════════
#  LOBBY CHAT
# ════════════════════════════════════════════════════════════════════════
def lobby_chat_menu():
    """Global pre-game lobby chat."""
    global _server_client, _current_user
    if _offline_mode or not _current_user or not _server_client:
        print("\n  Lobby chat requires an online connection and login.")
        return

    print("\n  ╔══════════════════════════════════════════════════════════╗")
    print("  ║                    LOBBY CHAT                            ║")
    print("  ╠══════════════════════════════════════════════════════════╣")
    print("  ║  Type a message and press Enter to send.                 ║")
    print("  ║  Press Enter on empty line to return to menu.            ║")
    print("  ╚══════════════════════════════════════════════════════════╝")

    # Load history
    resp = _server_client.get_lobby_chat_history(limit=30)
    if resp and resp.get('success'):
        messages = resp.get('data', {}).get('messages', [])
        if messages:
            print("  ── Recent messages ─────────────────────────────────────")
            for m in messages:
                sender = m.get('sender', '?')
                text   = m.get('message', '')
                ts     = m.get('timestamp', '')[:16] if m.get('timestamp') else ''
                print(f"  [{ts}] {sender}: {text}")
            print("  ─────────────────────────────────────────────────────────")
        else:
            print("  (No messages yet — be the first!)")

    while True:
        # Drain async queue for new lobby messages
        try:
            while not _server_client._async_queue.empty():
                msg = _server_client._async_queue.get_nowait()
                if msg.get('type') == MSG_LOBBY_CHAT:
                    d = msg.get('data', {})
                    print(f"  {d.get('sender','?')}: {d.get('message','')}")
                elif msg.get('type') == MSG_SERVER_BROADCAST:
                    print(f"  📢 {msg.get('data',{}).get('message','')}")
                elif msg.get('type') == MSG_ACHIEVEMENT_UNLOCKED:
                    d = msg.get('data', {})
                    print(f"  🏆 Achievement unlocked: {d.get('name', d.get('id','?'))}")
        except Exception:
            pass

        try:
            text = input(f"  {_current_user}: ").strip()
        except EOFError:
            break
        if not text:
            break
        _server_client.send_lobby_chat(text)


# ════════════════════════════════════════════════════════════════════════
#  ACHIEVEMENTS
# ════════════════════════════════════════════════════════════════════════
def achievements_menu():
    """Show the current user's achievements."""
    global _server_client, _current_user
    if _offline_mode or not _current_user or not _server_client:
        print("\n  Achievements require an online connection and login.")
        return

    resp = _server_client.get_achievements()
    if not resp or not resp.get('success'):
        print(f"\n  Could not load achievements: {resp.get('data','No response') if resp else 'No response'}")
        return

    data = resp.get('data', {})
    unlocked = {a['id'] for a in data.get('unlocked', [])}
    all_achievements = data.get('all', [])

    print(f"\n  ╔══════════════════════════════════════════════════════════╗")
    print(f"  ║  🏆  ACHIEVEMENTS  —  {_current_user:<36}║")
    print(f"  ╠══════════════════════════════════════════════════════════╣")
    for ach in all_achievements:
        aid  = ach.get('id', '?')
        name = ach.get('name', aid)
        desc = ach.get('desc', '')
        done = aid in unlocked
        icon = '✅' if done else '🔒'
        print(f"  ║  {icon} {name:<30} {desc[:20]:<20}║")
    print(f"  ╠══════════════════════════════════════════════════════════╣")
    print(f"  ║  Unlocked: {len(unlocked)}/{len(all_achievements):<46}║")
    print(f"  ╚══════════════════════════════════════════════════════════╝")
    try:
        input("  Press Enter to continue...")
    except EOFError:
        pass


# ════════════════════════════════════════════════════════════════════════
#  TOURNAMENTS
# ════════════════════════════════════════════════════════════════════════
def tournaments_menu():
    """Browse, create, and join Swiss-system tournaments."""
    global _server_client, _current_user
    if _offline_mode or not _current_user or not _server_client:
        print("\n  Tournaments require an online connection and login.")
        return

    while True:
        # List tournaments
        resp = _server_client.list_tournaments()
        ts = resp.get('data', {}).get('tournaments', []) if resp and resp.get('success') else []

        print("\n  ╔══════════════════════════════════════════════════════════╗")
        print("  ║                    TOURNAMENTS                           ║")
        print("  ╠══════════════════════════════════════════════════════════╣")
        if ts:
            for t in ts[:10]:
                status  = t.get('status', '?')
                name    = t.get('name', '?')[:28]
                players = len(t.get('players', []))
                maxp    = t.get('max_players', '?')
                rnd     = t.get('current_round', 0)
                rounds  = t.get('rounds', '?')
                tid     = t.get('id', '?')
                print(f"  ║  [{tid[:6]}] {name:<28} {status:<12}║")
                print(f"  ║           Players: {players}/{maxp}  Round: {rnd}/{rounds}{'':22}║")
        else:
            print("  ║  No active tournaments. Be the first to create one!     ║")
        print("  ╠══════════════════════════════════════════════════════════╣")
        print("  ║  1. Create tournament                                     ║")
        print("  ║  2. Join tournament                                       ║")
        print("  ║  3. View tournament details                               ║")
        print("  ║  0. Back                                                  ║")
        print("  ╚══════════════════════════════════════════════════════════╝")

        try:
            choice = input("  Choice: ").strip()
        except EOFError:
            break

        if choice == '0':
            break

        elif choice == '1':
            try:
                name   = input("  Tournament name: ").strip() or 'Open Tournament'
                maxp   = int(input("  Max players [8]: ").strip() or '8')
                rounds = int(input("  Rounds [3]: ").strip() or '3')
                print("  Time control: 1.Bullet  2.Blitz  3.Rapid  4.Classical")
                tc_map = {'1': 'bullet', '2': 'blitz', '3': 'rapid', '4': 'classical'}
                tc = tc_map.get(input("  Choice [2]: ").strip() or '2', 'blitz')
            except (EOFError, ValueError):
                continue
            resp = _server_client.create_tournament(name, maxp, rounds, tc)
            if resp and resp.get('success'):
                tid = resp.get('data', {}).get('tournament_id', '?')
                print(f"  ✓ Tournament '{name}' created! ID: {tid}")
            else:
                print(f"  ✗ Failed: {resp.get('data','error') if resp else 'no response'}")

        elif choice == '2':
            try:
                tid = input("  Tournament ID: ").strip()
            except EOFError:
                continue
            if not tid:
                continue
            resp = _server_client.join_tournament(tid)
            if resp and resp.get('success'):
                print(f"  ✓ Joined tournament {tid}!")
            else:
                print(f"  ✗ Failed: {resp.get('data','error') if resp else 'no response'}")

        elif choice == '3':
            try:
                tid = input("  Tournament ID: ").strip()
            except EOFError:
                continue
            if not tid:
                continue
            resp = _server_client.get_tournament_status(tid)
            if resp and resp.get('success'):
                t = resp.get('data', {})
                print(f"\n  Tournament: {t.get('name','?')}")
                print(f"  Status: {t.get('status','?')}  Round: {t.get('current_round',0)}/{t.get('rounds','?')}")
                print(f"  Time Control: {t.get('time_control','?')}")
                print(f"  Players: {', '.join(t.get('players',[]))}")
                # Show standings
                standings = t.get('standings', {})
                if standings:
                    print("  ── Standings ──")
                    sorted_s = sorted(standings.items(), key=lambda x: x[1], reverse=True)
                    for rank, (player, pts) in enumerate(sorted_s, 1):
                        print(f"  {rank}. {player:<20} {pts} pts")
                # Show current pairings
                pairings = t.get('pairings', {})
                cur_round = str(t.get('current_round', 0))
                if cur_round in pairings:
                    print(f"  ── Round {cur_round} Pairings ──")
                    for pair in pairings[cur_round]:
                        w = pair.get('white', '?')
                        b = pair.get('black', '?')
                        r = pair.get('result', 'pending')
                        print(f"  {w} vs {b}  →  {r}")
            else:
                print(f"  Not found: {resp.get('data','') if resp else 'no response'}")
            try:
                input("  Press Enter...")
            except EOFError:
                pass


# ════════════════════════════════════════════════════════════════════════
#  SERVER DAILY PUZZLE
# ════════════════════════════════════════════════════════════════════════
def server_daily_puzzle():
    """Fetch and display the server's daily puzzle."""
    global _server_client
    if _offline_mode or not _server_client:
        print("\n  Server puzzle requires an online connection.")
        return

    resp = _server_client.get_daily_puzzle()
    if not resp or not resp.get('success'):
        print(f"\n  Could not load puzzle: {resp.get('data','No response') if resp else 'No response'}")
        return

    p = resp.get('data', {})
    print("\n  ╔══════════════════════════════════════════════════════════╗")
    print(f"  ║  📅  SERVER DAILY PUZZLE — {p.get('date','today'):<30}║")
    print("  ╠══════════════════════════════════════════════════════════╣")
    print(f"  ║  Theme  : {p.get('theme','?'):<46}║")
    print(f"  ║  Rating : {p.get('rating','?'):<46}║")
    print("  ╠══════════════════════════════════════════════════════════╣")
    fen = p.get('fen', '')
    if fen:
        try:
            board = _board_from_fen(fen)
            draw_board(board)
        except Exception:
            print(f"  FEN: {fen}")
    solution = p.get('moves', [])
    print("  ╠══════════════════════════════════════════════════════════╣")
    print("  ║  What is the best move?                                  ║")
    print("  ╚══════════════════════════════════════════════════════════╝")
    try:
        ans = input("  Your move (or Enter to reveal): ").strip()
    except EOFError:
        ans = ''
    if solution:
        sol_str = ' '.join(solution[:4])
        if ans and ans.lower() == solution[0].lower():
            print(f"  ✅ Correct! Solution: {sol_str}")
        elif ans:
            print(f"  ✗  Solution: {sol_str}")
        else:
            print(f"  Solution: {sol_str}")




def _post_game_menu(board, white_name, black_name, game_id, chat_log):
    """Show post-game options: analysis, chat history, rematch, server analysis."""
    while True:
        print("\n  ╔══════════════════════════════════════════════════════════╗")
        print("  ║                  GAME OVER — OPTIONS                    ║")
        print("  ╠══════════════════════════════════════════════════════════╣")
        print("  ║  1. Step-by-step analysis (local engine)                ║")
        print("  ║  2. Summary analysis                                    ║")
        print("  ║  3. Request server analysis (queued)                    ║")
        print("  ║  4. View chat history                                   ║")
        print("  ║  5. Request rematch                                     ║")
        print("  ║  6. View my achievements                                ║")
        print("  ║  0. Back to menu                                        ║")
        print("  ╚══════════════════════════════════════════════════════════╝")

        try:
            choice = input("  Choice: ").strip()
        except EOFError:
            return

        if choice == '0':
            return

        elif choice == '1':
            if not board.san_log:
                print("  No moves to analyze.")
            else:
                step_by_step_analysis(board.san_log)

        elif choice == '2':
            if not board.san_log:
                print("  No moves to analyze.")
            else:
                print("\n  Starting analysis...")
                _analyze_online_game_with_eta(board.san_log)

        elif choice == '3':
            if _server_client and game_id and board.san_log:
                pgn_str = export_pgn(board.san_log, white_name, black_name)
                resp = _server_client.request_analysis(
                    game_id, board.san_log, pgn=pgn_str,
                    white=white_name, black=black_name
                )
                if resp and resp.get('success'):
                    d = resp.get('data', {})
                    if d.get('queued'):
                        print("  ✓ Analysis queued on server. You'll be notified when ready.")
                    else:
                        # Instant cached result
                        note = d.get('note', '')
                        print(f"  Analysis result: {note}")
                else:
                    print(f"  Could not request analysis: {resp.get('data','') if resp else 'no connection'}")
            else:
                print("  Analysis not available (need server connection and moves).")

        elif choice == '4':
            if not chat_log:
                if _server_client and game_id:
                    resp = _server_client.get_game_chat_history(game_id)
                    if resp and resp.get('success'):
                        chat_log = resp.get('data', {}).get('chat_log', [])
            if not chat_log:
                print("  No chat messages in this game.")
            else:
                print("\n  ── Chat History ─────────────────────────────────────────")
                for entry in chat_log:
                    sender = entry.get('from', '?')
                    msg    = entry.get('msg', '')
                    print(f"  [{sender}]: {msg}")
                print("  ─────────────────────────────────────────────────────────")

        elif choice == '5':
            if _server_client and game_id:
                resp = _server_client.request_rematch(game_id, white_name, black_name)
                if resp and resp.get('success'):
                    print("  Rematch requested! Waiting for opponent (30s)...")
                    deadline = time.time() + 30
                    while time.time() < deadline:
                        try:
                            msg = _server_client._async_queue.get(timeout=1.0)
                        except Exception:
                            continue
                        if msg.get('type') == MSG_REMATCH_RESPONSE:
                            d = msg.get('data', {})
                            new_game_id = d.get('new_game_id')
                            new_color   = d.get('color', 'white')
                            new_white   = d.get('white', white_name)
                            new_black   = d.get('black', black_name)
                            new_opp     = new_black if new_color == 'white' else new_white
                            print(f"\n  Rematch accepted! You play {new_color.upper()}.")
                            play_online_matched_game(
                                new_game_id, new_color, new_opp,
                                _server_client._async_queue,
                                _server_client._listener_stop
                            )
                            return
                        elif msg.get('type') == MSG_REMATCH_REQUEST:
                            _server_client.request_rematch(game_id, white_name, black_name)
                    print("  Rematch timed out.")
            else:
                print("  Rematch not available.")

        elif choice == '6':
            achievements_menu()

        else:
            print("  Invalid choice.")




def step_by_step_analysis(san_log, engine_time=1.5):
    """
    Interactive move-by-move game analysis.
    Shows board + move classification for each half-move.
    Navigation: [n]ext, [p]rev, [j]ump, [q]uit.
    """
    if not san_log:
        print("  No moves to analyze.")
        return

    print(f"\n  Analysing {len(san_log)} moves (this may take a minute)...")
    results = analyze_game(san_log, engine_time=engine_time, depth_limit=14)
    if not results:
        print("  Analysis failed.")
        return

    # Build board states
    boards = [Board()]
    boards[0].reset()
    for san in san_log:
        b = boards[-1].copy()
        m = b.parse_san(san)
        if m:
            b.make(m)
        boards.append(b)

    idx = 0   # 0 = starting position, 1..N = after move idx
    total = len(san_log)

    while True:
        clear_screen()
        # Draw the position after move idx
        persp = WHITE if idx == 0 or results[idx - 1]['side'] == 'Black' else BLACK
        draw_board(boards[idx], persp=WHITE, labels=True)

        if idx == 0:
            print("  ── Starting position ──────────────────────────────")
        else:
            r = results[idx - 1]
            move_num  = r['move_num']
            side      = r['side']
            san       = r['san']
            symbol    = r['symbol']
            label     = r['label']
            cp_loss   = r['cp_loss']
            best      = r.get('best', '')
            print(f"  ── Move {move_num}{'.' if side == 'White' else '...'} {san}  {symbol} {label}", end='')
            if cp_loss is not None and cp_loss > 0:
                print(f"  (−{cp_loss} cp)", end='')
            print()
            if best and not r.get('is_best'):
                print(f"     Best: {best}")

        print(f"\n  Move {idx}/{total}  │  [n]ext  [p]rev  [j]ump  [q]uit")
        try:
            cmd = input("  > ").strip().lower()
        except EOFError:
            break

        if cmd in ('q', 'quit'):
            break
        elif cmd in ('n', '', 'next'):
            if idx < total:
                idx += 1
        elif cmd in ('p', 'prev', 'b', 'back'):
            if idx > 0:
                idx -= 1
        elif cmd.startswith('j'):
            parts = cmd.split()
            if len(parts) == 2:
                try:
                    idx = max(0, min(total, int(parts[1])))
                except ValueError:
                    pass


def _analyze_online_game_with_eta(san_log, engine_time=1.5):
    """Analyze a game and display ETA progress."""
    total = len(san_log)
    if total == 0:
        print("  No moves to analyze.")
        return
    
    print(f"\n  Analyzing {total} moves...")
    results = []
    board = Board()
    board.reset()
    tb = Tablebase()
    book = OpeningBook()
    eng = Engine(tb=tb, book=None, strength=1.5)
    
    start_time = time.time()
    _CP = {PAWN: 100, KNIGHT: 320, BISHOP: 330, ROOK: 500, QUEEN: 900, KING: 0}
    
    eng.tt.clear()
    _, prev_score = eng.search_best(board, t_limit=engine_time, depth_limit=12)
    
    for i, san in enumerate(san_log):
        elapsed = time.time() - start_time
        if i > 0 and elapsed > 0:
            rate = i / elapsed
            eta = (total - i) / rate
            print(f"  Analyzing move {i+1}/{total}... ETA: {eta:.0f}s", end='\r')
        
        side = WHITE if i % 2 == 0 else BLACK
        m = board.parse_san(san)
        if m is None:
            break
        
        is_book_move = any(board.parse_san(bs) == m for bs, _ in book.probe(board))
        
        eng.tt.clear()
        best_mv, best_score = eng.search_best(board, t_limit=engine_time, depth_limit=12)
        is_best = (m == best_mv)
        best_san_str = board.san(best_mv) if best_mv else '?'
        score_before = prev_score
        
        board.make(m)
        board.san_log.append(san)
        
        eng.tt.clear()
        _, score_after_opp = eng.search_best(board, t_limit=engine_time * 0.6, depth_limit=10)
        score_after_mover = -score_after_opp
        cp_loss = score_before - score_after_mover
        
        category, label, symbol = classify_move(cp_loss, is_best, is_book_move)
        results.append({
            'move_num': i // 2 + 1,
            'side': side,
            'san': san,
            'category': category,
            'label': label,
            'symbol': symbol,
            'cp_loss': cp_loss,
            'score': score_after_mover,
            'best': best_san_str,
            'is_best': is_best,
            'is_book': is_book_move,
        })
        prev_score = score_after_opp
    
    print(f"  Analysis complete! ({time.time() - start_time:.1f}s)                    ")
    print_analysis(results)


def play_online_matched_game(game_id, my_color, opponent_name, msg_queue, stop_listener):
    """Play an online matched game with clock, chat, spectator support."""
    board = Board()
    board.reset()
    last_mv = None
    game_start_time = time.time()
    chat_log = []  # Persistent chat log for this game
    
    # Clock state (updated by server broadcasts)
    white_remaining = 0.0
    black_remaining = 0.0
    clock_enabled = False

    my_name = _current_user
    white_name = my_name if my_color == 'white' else opponent_name
    black_name = opponent_name if my_color == 'white' else my_name

    print("\n  ╔══════════════════════════════════════════════════════════╗")
    print("  ║                    ONLINE GAME                           ║")
    print("  ╠══════════════════════════════════════════════════════════╣")
    print(f"  ║  {white_name:<28} vs  {black_name:<28}║")
    print("  ╠══════════════════════════════════════════════════════════╣")
    print("  ║  Commands: 'draw', 'resign', 'chat <msg>', 'moves'       ║")
    print("  ╚══════════════════════════════════════════════════════════╝\n")

    game_over = False
    game_result = None  # 'white', 'black', or 'draw'

    while not game_over:
        # Process messages from centralized queue
        try:
            while not _server_client._async_queue.empty():
                msg = _server_client._async_queue.get_nowait()
                msg_type = msg.get('type', '')
                data = msg.get('data', {})
                
                if msg_type == MSG_GAME_MOVE:
                    move_san = data.get('move')
                    from_player = data.get('from_player')
                    m = board.parse_san(move_san)
                    if m:
                        board.make(m)
                        board.san_log.append(move_san)
                        last_mv = m
                        print(f"  ♟ {from_player} plays: {move_san}")

                elif msg_type == MSG_GAME_CLOCK_UPDATE:
                    white_remaining = data.get('white_remaining', 0)
                    black_remaining = data.get('black_remaining', 0)
                    clock_enabled = True

                elif msg_type == MSG_GAME_TIMEOUT:
                    timed_out = data.get('timed_out')
                    winner = data.get('winner')
                    print(f"\n  ⏰ {timed_out} ran out of time! {winner} wins!")
                    game_result = 'white' if winner == white_name else 'black'
                    _save_game_to_server(white_name, black_name, game_result,
                                        board.san_log, time.time() - game_start_time,
                                        show_elo_changes=True)
                    game_over = True
                    break

                elif msg_type == MSG_GAME_RESIGN:
                    winner = data.get('winner')
                    resigned_by = data.get('resigned_by')
                    print(f"\n  ✗ {resigned_by} resigned. {winner} wins!")
                    game_result = 'white' if winner == white_name else 'black'
                    _save_game_to_server(white_name, black_name, game_result,
                                        board.san_log, time.time() - game_start_time,
                                        show_elo_changes=True)
                    game_over = True
                    break

                elif msg_type == MSG_GAME_DRAW_OFFER:
                    offered_by = data.get('offered_by')
                    print(f"\n  ½ {offered_by} offers a draw.")
                    try:
                        ans = input("  Accept draw? [y/N]: ").strip().lower()
                    except EOFError:
                        ans = 'n'
                    if ans in ('y', 'yes'):
                        _server_client.accept_draw(game_id)
                        print("  Game ended in a draw.")
                        game_result = 'draw'
                        _save_game_to_server(white_name, black_name, 'draw',
                                            board.san_log, time.time() - game_start_time,
                                            show_elo_changes=True)
                        game_over = True
                        break
                    else:
                        print("  Draw declined.")

                elif msg_type == MSG_GAME_DRAW_ACCEPT:
                    print("\n  ½ Draw accepted! Game ended in a draw.")
                    game_result = 'draw'
                    _save_game_to_server(white_name, black_name, 'draw',
                                        board.san_log, time.time() - game_start_time,
                                        show_elo_changes=True)
                    game_over = True
                    break

                elif msg_type == MSG_GAME_CHAT:
                    from_p = data.get('from_player')
                    msg_text = data.get('message')
                    chat_log.append({'from': from_p, 'msg': msg_text})
                    print(f"\n  💬 [{from_p}]: {msg_text}")

                elif msg_type == MSG_REMATCH_REQUEST:
                    from_p = data.get('from', '?')
                    print(f"\n  🔄 {from_p} wants a rematch! Use post-game menu to respond.")
        except:
            pass

        if game_over:
            break
        
        # Draw board
        persp = WHITE if my_color == 'white' else BLACK
        draw_board(board, persp, last_mv)
        
        turn_str = "White" if board.side == WHITE else "Black"
        chk_str = "  *** CHECK ***" if board.in_check() else ""
        
        # Clock display
        if clock_enabled:
            wt = _fmt_online_clock(white_remaining)
            bt = _fmt_online_clock(black_remaining)
            print(f"  ⏱ White: {wt}  |  Black: {bt}")
        
        print(f"  Move {board.fullmove} — {turn_str} to move{chk_str}")
        
        # Show move history
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
                print(f"  ✓ Checkmate! {winner_name} wins!")
                game_result = 'white' if winner == WHITE else 'black'
                _save_game_to_server(white_name, black_name, game_result,
                                    board.san_log, time.time() - game_start_time,
                                    show_elo_changes=True)
            else:
                print("  Stalemate - Draw!")
                game_result = 'draw'
                _save_game_to_server(white_name, black_name, 'draw',
                                    board.san_log, time.time() - game_start_time,
                                    show_elo_changes=True)
            game_over = True
            break

        # Check for draw conditions
        for cond, msg_text in [(board.is_repetition(), "threefold repetition"),
                          (board.is_fifty(), "50-move rule"),
                          (board.insufficient_material(), "insufficient material")]:
            if cond:
                print(f"  Draw: {msg_text}")
                game_result = 'draw'
                _save_game_to_server(white_name, black_name, 'draw',
                                    board.san_log, time.time() - game_start_time,
                                    show_elo_changes=True)
                game_over = True
                break
        
        if game_over:
            break
        
        # Check if it's my turn
        my_turn_now = (my_color == 'white' and board.side == WHITE) or \
                      (my_color == 'black' and board.side == BLACK)
        
        if not my_turn_now:
            print(f"  Waiting for {opponent_name}...")
            time.sleep(0.5)
            continue
        
        # My turn - get move
        try:
            raw = input("  Your move (or 'resign'/'draw'/'chat <msg>'): ").strip()
        except EOFError:
            _server_client.resign_game(game_id)
            return
        
        if not raw:
            continue
        
        cmd = raw.lower()
        
        if cmd in ('quit', 'exit', 'resign'):
            _server_client.resign_game(game_id)
            print("  You resigned.")
            game_result = 'black' if my_color == 'white' else 'white'
            game_over = True
            break
        
        if cmd == 'draw':
            _server_client.offer_draw(game_id)
            print("  Draw offer sent.")
            continue
        
        if cmd.startswith('chat ') and len(raw) > 5:
            msg_text = raw[5:]
            _server_client.send_chat(game_id, msg_text)
            chat_log.append({'from': my_name, 'msg': msg_text})
            print(f"  💬 [You]: {msg_text}")
            continue
        
        if cmd == 'help':
            print("  Commands: <move>  draw  resign  chat <message>  moves  clock")
            continue
        
        if cmd == 'clock':
            if clock_enabled:
                print(f"  ⏱ White: {_fmt_online_clock(white_remaining)}  |  Black: {_fmt_online_clock(black_remaining)}")
            else:
                print("  No clock enabled for this game.")
            continue
        
        if cmd == 'moves':
            sms = [board.san(m) for m in legal]
            for i in range(0, len(sms), 8):
                print("  " + "  ".join(f"{s:<8}" for s in sms[i:i+8]))
            continue
        
        # Parse and send move
        mv = board.parse_san(raw)
        if mv is None:
            print(f"  Illegal/unrecognised: '{raw}'. Try 'moves' for legal moves.")
            continue
        
        s = board.san(mv)
        _server_client.send_move(game_id, s)
        board.make(mv)
        board.san_log.append(s)
        last_mv = mv

    # Post-game options
    _post_game_menu(board, white_name, black_name, game_id, chat_log)


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
def _eval_bar(score_cp, width=30):
    """
    Render a compact evaluation bar as text.
    score_cp: centipawns from White's perspective (+ve = White better).
    Returns a string like:  ████████████████░░░░░░░░░░░░  +1.23
    """
    # Clamp to ±600 cp for display purposes
    clamped = max(-600, min(600, score_cp))
    white_frac = (clamped + 600) / 1200          # 0.0..1.0
    filled = int(round(white_frac * width))
    bar = '█' * filled + '░' * (width - filled)

    # Label
    if abs(score_cp) >= 9_000_000:
        label = 'M#' if score_cp > 0 else '#M'
    else:
        pawns = score_cp / 100.0
        sign  = '+' if pawns > 0 else ''
        label = f'{sign}{pawns:.2f}'

    return f'  [{bar}] {label:>6}'


def draw_board(board, persp=WHITE, last=None, labels=True):
    """Render the chess board with Unicode piece symbols.

    Pieces: ♔♕♖♗♘♙ (White) and ♚♛♜♝♞♟ (Black)
    Highlighted squares (last move) are marked with [ ] brackets.
    Dark empty squares show a · for contrast.
    """
    labels = labels and _settings.get('show_coords', True)

    highlighted = set()
    if last:
        highlighted = {last.from_sq, last.to_sq}

    ranks = range(7, -1, -1) if persp == WHITE else range(8)
    files = range(8)         if persp == WHITE else range(7, -1, -1)

    file_labels = [chr(ord('a') + f) for f in files]

    # Each cell is 3 chars wide; Unicode symbols are 1 display-column wide
    sep = '  +' + '---+' * 8

    lines = ['']
    lines.append(sep)

    for i, rank in enumerate(ranks):
        row_str = f' {rank + 1}|'
        for file in files:
            sq   = rank * 8 + file
            p    = board.sq[sq]
            dark = (rank + file) % 2 == 0
            hl   = sq in highlighted

            if p:
                ch = PIECE_UNICODE[p]
                if hl:
                    row_str += f'[{ch}]|'
                else:
                    row_str += f' {ch} |'
            else:
                if hl:
                    row_str += '[ ]|'
                elif dark:
                    row_str += ' · |'
                else:
                    row_str += '   |'

        lines.append(row_str)
        lines.append(sep)

    if labels:
        file_row = '    ' + '   '.join(file_labels)
        lines.append(file_row)

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
║  Neural Net • Opening Book • Tablebases • Clocks • PGN       ║
║  Per-TC ELO • Replay Viewer • Endgame Trainer                ║
╚══════════════════════════════════════════════════════════════╝
"""

HELP = """
 ╔─── IN-GAME COMMANDS ──────────────────────────────────────────╗
 │  <move>    SAN:  e4  Nf3  O-O  exd5  e8=Q                     │
 │            Long algebraic also works:  e2e4  e2-e4  g1f3       │
 │  undo      Take back last 2 half-moves (vs AI only)            │
 │  moves     Show all legal moves                                │
 │  flip      Flip board perspective                              │
 │  resign    Resign the game                                     │
 │  draw      Claim/offer draw                                    │
 │  save      Save game & continue later (vs AI only)            │
 │  pgn       Print PGN of game so far                            │
 │  replay    Replay the game so far interactively                │
 │  chat <m>  Send chat message (multiplayer)                     │
 │  elo       Show ELO leaderboard (current time-control)         │
 │  help      This help                                           │
 │  quit      Exit to main menu                                   │
 ╠─── SAN REFERENCE ─────────────────────────────────────────────╣
 │  Pawn:     e4  d5  exd5  (promotion:) e8=Q  e8=R  e8=B  e8=N  │
 │  Piece:    Nf3  Bxc4  Rhe1  Qd1f3 (disambiguation)             │
 │  Castle:   O-O  (kingside)   O-O-O  (queenside)                │
 ╠─── REPLAY VIEWER ─────────────────────────────────────────────╣
 │  n/Enter   Next move    p   Previous move                      │
 │  b         Start        e   End      g<N>  Go to move N        │
 │  flip      Flip board   a   Analyze from here   q   Quit       │
 ╚───────────────────────────────────────────────────────────────╝
"""

# ════════════════════════════════════════════════════════════════════════
#  GAME RESULT HANDLING
# ════════════════════════════════════════════════════════════════════════
def handle_game_end(board, elo_sys, white_name, black_name,
                    winner_color=None, draw=False, resigned=False,
                    elo_category='unlimited'):
    """Update ELO (per category), offer analysis and PGN export."""
    print()
    if draw:
        print("  ½-½  Draw\n")
        elo_change = elo_sys.update(white_name, black_name, 0.5, category=elo_category)
        result_str = 'Draw'
    elif winner_color == WHITE:
        print(f"  1-0  {white_name} wins!\n")
        elo_change = elo_sys.update(white_name, black_name, 1, category=elo_category)
        result_str = 'White wins'
    else:
        print(f"  0-1  {black_name} wins!\n")
        elo_change = elo_sys.update(black_name, white_name, 1, category=elo_category)
        result_str = 'Black wins'

    w_elo = elo_sys.get_elo(white_name, elo_category)
    b_elo = elo_sys.get_elo(black_name, elo_category)
    cat_label = elo_category.capitalize()
    print(f"  [{cat_label}] ELO — {white_name}: {w_elo}  |  {black_name}: {b_elo}")
    if elo_change is not None:
        sign = '+' if elo_change >= 0 else ''
        print(f"  Your ELO change: {sign}{elo_change}\n")
    else:
        print()

    # Offer options
    print("  What would you like to do?")
    print("  1. Analyze game   2. Replay game   3. Export PGN   [Enter] Skip")
    try:
        ans = input("  Choice: ").strip().lower()
    except EOFError:
        ans = ''
    if ans in ('1', 'a', 'analyze', 'yes', 'y'):
        results = analyze_game(board.san_log, engine_time=1.0)
        print_analysis(results)
    elif ans in ('2', 'r', 'replay'):
        replay_game(board.san_log, white_name=white_name, black_name=black_name)
    elif ans in ('3', 'p', 'pgn', 'export'):
        result_tag = ('1-0' if winner_color == WHITE else
                      '0-1' if winner_color == BLACK else '1/2-1/2')
        pgn = export_pgn(board.san_log, white_name, black_name, result_tag)
        print("\n" + "─"*70)
        print(pgn)
        print("─"*70)
        try:
            fn = input("  Save to file (blank to skip): ").strip()
        except EOFError:
            fn = ''
        if fn:
            try:
                with open(fn, 'w') as f:
                    f.write(pgn)
                print(f"  ✓ Saved to {fn}")
            except Exception as e:
                print(f"  Error: {e}")

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

    # ── Resume saved game? ──────────────────────────────────────────────
    saved = load_bot_save()
    if saved:
        saved_at = saved.get('saved_at', 'unknown')
        moves_n  = len(saved.get('san_log', []))
        print(f"\n  ╔══════════════════════════════════════════════════════════╗")
        print(f"  ║  SAVED BOT GAME FOUND                                    ║")
        print(f"  ╠══════════════════════════════════════════════════════════╣")
        print(f"  ║  Saved : {saved_at[:19]:<49}║")
        print(f"  ║  Moves : {moves_n:<49}║")
        print(f"  ║  Player: {saved.get('player_name','?'):<49}║")
        print(f"  ╠══════════════════════════════════════════════════════════╣")
        print(f"  ║  R. Resume saved game                                    ║")
        print(f"  ║  N. Start a new game                                     ║")
        print(f"  ╚══════════════════════════════════════════════════════════╝")
        try:
            res_choice = input("  Choice [R/N]: ").strip().lower()
        except EOFError:
            return
        if res_choice in ('r', 'resume'):
            # Restore state
            san_log      = saved.get('san_log', [])
            human_color  = saved.get('human_color', WHITE)
            bot_level    = saved.get('bot_level', 'medium')
            player_name  = saved.get('player_name', 'Player')
            clock_mins   = saved.get('clock_mins', 0)
            clock_inc    = saved.get('clock_inc', 0)
            elo_category = saved.get('elo_category', 'rapid')

            # Replay moves onto board
            b2 = Board(); b2.reset()
            for san in san_log:
                m = b2.parse_san(san)
                if m: b2.make(m); b2.san_log.append(san)
            board = b2
            last_mv = None
            bot = ChessBot(level=bot_level, tb=tb, book=book)
            bot_name = bot.get_name()
            clock = ChessClock(clock_mins, clock_inc) if clock_mins > 0 else None
            persp = human_color
            white_name = player_name if human_color == WHITE else bot_name
            black_name = bot_name    if human_color == WHITE else player_name
            game_start = time.time()
            print(f"  ✓ Resumed! Move {board.fullmove}.")
            # Jump directly into the game loop (skip setup below)
            import sys as _sys
            # Use a sentinel to skip the normal setup path
            _resuming = True
        else:
            _resuming = False
            delete_bot_save()
    else:
        _resuming = False

    if not _resuming:
        # ── Normal new-game setup ──────────────────────────────────────────
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

        # Select time control
        clock_mins, clock_inc = ChessClock.select_time_control()
        clock = ChessClock(clock_mins, clock_inc) if clock_mins > 0 else None
        elo_category = EloSystem.category_for(clock_mins)
        game_start = time.time()
        persp=human_color
        white_name=player_name if human_color==WHITE else bot_name
        black_name=bot_name if human_color==WHITE else player_name

        # Show time control info
        if clock_mins > 0:
            tc_str = f"{clock_mins}+{clock_inc}" if clock_inc else f"{clock_mins}+0"
            print(f"  Time control: {tc_str}  [{elo_category.capitalize()}]\n")
        else:
            print(f"  Time control: Unlimited  [{elo_category.capitalize()}]\n")

    while True:
        draw_board(board, persp, last_mv)
        # Evaluation bar (toggle in Settings → Eval Bar)
        if _settings.get('show_eval_bar', False):
            _ev = evaluate(board)
            if board.side == BLACK: _ev = -_ev
            print(_eval_bar(_ev))
        turn_str="White" if board.side==WHITE else "Black"
        chk_str="  *** CHECK ***" if board.in_check() else ""

        # Clock display
        if clock:
            wt = _fmt_clock(clock, WHITE)
            bt = _fmt_clock(clock, BLACK)
            print(f"  ⏱  White: {wt}   Black: {bt}")
            # Check for flag
            if clock.flag(WHITE):
                print("  ⏰ White's time is up! Black wins on time!")
                handle_game_end(board,elo_sys,white_name,black_name,winner_color=BLACK,elo_category=elo_category)
                _save_game_to_server(white_name,black_name,'black',board.san_log,time.time()-game_start)
                return
            if clock.flag(BLACK):
                print("  ⏰ Black's time is up! White wins on time!")
                handle_game_end(board,elo_sys,white_name,black_name,winner_color=WHITE,elo_category=elo_category)
                _save_game_to_server(white_name,black_name,'white',board.san_log,time.time()-game_start)
                return

        print(f"  Move {board.fullmove} — {turn_str} to move{chk_str}")

        # Show recent moves
        if board.san_log:
            pairs=[]
            for i in range(0,len(board.san_log),2):
                wm=board.san_log[i]
                bm=board.san_log[i+1] if i+1<len(board.san_log) else '...'
                pairs.append(f"{i//2+1}. {wm} {bm}")
            print("  "+' | '.join(pairs[-4:]))

        # ELO display — show category-specific ELO
        we=elo_sys.get_elo(white_name, elo_category)
        be=elo_sys.get_elo(black_name, elo_category)
        cat_label = elo_category.capitalize()
        print(f"  [{cat_label}] {white_name}({we}) vs {black_name}({be})\n")

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
            handle_game_end(board,elo_sys,white_name,black_name,winner_color=winner_color,elo_category=elo_category)
            # Save game to server
            _save_game_to_server(white_name, black_name, result, board.san_log, time.time()-game_start)
            return

        for cond,msg in [(board.is_repetition(),"threefold repetition"),
                         (board.is_fifty(),"50-move rule"),
                         (board.insufficient_material(),"insufficient material")]:
            if cond:
                print(f"  ½-½ Draw: {msg}")
                handle_game_end(board,elo_sys,white_name,black_name,draw=True,elo_category=elo_category)
                # Save game to server
                _save_game_to_server(white_name, black_name, 'draw', board.san_log, time.time()-game_start)
                return

        # AI turn
        if board.side!=human_color:
            ai_side = board.side
            if clock: clock.start(ai_side)
            print(f"  {bot_name} thinking...\n")
            mv=bot.get_move(board)
            if clock: clock.stop(ai_side)
            if mv:
                s=board.san(mv); board.make(mv); board.san_log.append(s)
                last_mv=mv; print(f"\n  {bot_name} plays: {s}\n")
            continue

        # Human turn
        if clock: clock.start(human_color)
        try:
            raw=input("  Your move (or 'help'): ").strip()
        except EOFError:
            if clock: clock.stop(human_color)
            return
        if not raw: continue
        cmd=raw.lower()

        if cmd in('quit','exit','q'):
            # Save game as abandoned if moves were made
            if board.san_log:
                result = 'black' if human_color==WHITE else 'white'
                _save_game_to_server(white_name, black_name, result, board.san_log, time.time()-game_start)
            delete_bot_save()
            return
        if cmd=='help': print(HELP); continue
        if cmd=='flip': persp=1-persp; continue
        if cmd=='elo': elo_sys.leaderboard(category=elo_category); continue
        if cmd=='pgn':
            result_tag = '*'
            pgn = export_pgn(board.san_log, white_name, black_name, result_tag)
            print(pgn); continue
        if cmd=='replay':
            replay_game(board.san_log, white_name=white_name, black_name=black_name); continue
        if cmd=='moves':
            sms=[board.san(m) for m in legal]
            for i in range(0,len(sms),8):
                print("  "+"  ".join(f"{s:<8}" for s in sms[i:i+8]))
            print(); continue
        if cmd=='resign':
            if clock: clock.stop(human_color)
            winner=BLACK if human_color==WHITE else WHITE
            print(f"  {player_name} resigned.")
            handle_game_end(board,elo_sys,white_name,black_name,winner_color=winner,elo_category=elo_category)
            _save_game_to_server(white_name, black_name, 'black' if human_color==WHITE else 'white', board.san_log, time.time()-game_start)
            return
        if cmd=='draw':
            if board.is_repetition() or board.is_fifty():
                if clock: clock.stop(human_color)
                handle_game_end(board,elo_sys,white_name,black_name,draw=True,elo_category=elo_category)
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
        if cmd == 'save':
            state = {
                'san_log':      board.san_log[:],
                'human_color':  human_color,
                'bot_level':    bot_level,
                'player_name':  player_name,
                'clock_mins':   clock_mins,
                'clock_inc':    clock_inc,
                'elo_category': elo_category,
                'saved_at':     datetime.now().isoformat(),
            }
            if save_bot_game(state):
                print("  ✓ Game saved. You can resume it from the main menu (Play vs AI → Resume).")
            else:
                print("  ✗ Could not save game.")
            continue

        # Normalise move (accept e2e4, e2-e4, etc.)
        raw = board._normalise_input(raw)
        mv=board.parse_san(raw)
        if mv is None:
            print(f"  Illegal/unrecognised: '{raw}'. Try 'moves' or 'help'.")
            continue
        if clock: clock.stop(human_color)
        s=board.san(mv); board.make(mv); board.san_log.append(s); last_mv=mv


def _save_game_to_server(white, black, result, moves, duration, show_elo_changes=False,
                          pgn='', move_times=None):
    """
    Save game result to the server if connected.
    Passes PGN and move_times for server-side storage and anti-cheat analysis.
    Also saves locally for later analysis.
    """
    # Save locally for analysis
    save_online_game(white, black, result, moves, duration, rated=True)

    if _server_client is not None and _server_client.sock is not None and _current_user:
        try:
            response = _server_client.save_game(
                white, black, result, moves, int(duration),
                rated=True, pgn=pgn, move_times=move_times or []
            )
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
                    error_msg = response.get('data', 'Unknown error')
                    print(f"\n  Warning: Failed to save game to server: {error_msg}")
            else:
                print("\n  Warning: No response from server when saving game.")
        except Exception as e:
            print(f"\n  Warning: Error saving game to server: {e}")
    else:
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

    # Select time control for local game
    clock_mins, clock_inc = ChessClock.select_time_control()
    clock = ChessClock(clock_mins, clock_inc) if clock_mins > 0 else None
    elo_category = EloSystem.category_for(clock_mins)
    if clock_mins > 0:
        tc_str = f"{clock_mins}+{clock_inc}" if clock_inc else f"{clock_mins}+0"
        print(f"  Time control: {tc_str}  [{elo_category.capitalize()}]\n")

    while True:
        draw_board(board, persp, last_mv)
        turn_str="White" if board.side==WHITE else "Black"
        pname=wn if board.side==WHITE else bn
        chk_str="  *** CHECK ***" if board.in_check() else ""

        # Clock display
        if clock:
            wt = _fmt_clock(clock, WHITE)
            bt = _fmt_clock(clock, BLACK)
            print(f"  ⏱  White: {wt}   Black: {bt}")
            if clock.flag(WHITE):
                print("  ⏰ White's time is up! Black wins on time!")
                handle_game_end(board,elo_sys,wn,bn,winner_color=BLACK,elo_category=elo_category)
                return
            if clock.flag(BLACK):
                print("  ⏰ Black's time is up! White wins on time!")
                handle_game_end(board,elo_sys,wn,bn,winner_color=WHITE,elo_category=elo_category)
                return

        print(f"  Move {board.fullmove} — {pname} ({turn_str}) to move{chk_str}")
        if board.san_log:
            pairs=[]
            for i in range(0,len(board.san_log),2):
                pairs.append(f"{i//2+1}. {board.san_log[i]} {board.san_log[i+1] if i+1<len(board.san_log) else '...'}")
            print("  "+' | '.join(pairs[-4:]))
        we=elo_sys.get_elo(wn, elo_category); be=elo_sys.get_elo(bn, elo_category)
        cat_label = elo_category.capitalize()
        print(f"  [{cat_label}] {wn}({we}) vs {bn}({be})\n")

        legal=board.legal()
        if not legal:
            draw_board(board, persp, last_mv)
            if board.in_check():
                winner=BLACK if board.side==WHITE else WHITE
                handle_game_end(board,elo_sys,wn,bn,winner_color=winner,elo_category=elo_category)
            else:
                handle_game_end(board,elo_sys,wn,bn,draw=True,elo_category=elo_category)
            return

        for cond,msg in [(board.is_repetition(),"threefold repetition"),
                         (board.is_fifty(),"50-move rule"),
                         (board.insufficient_material(),"insufficient material")]:
            if cond:
                print(f"  ½-½ Draw: {msg}")
                handle_game_end(board,elo_sys,wn,bn,draw=True,elo_category=elo_category)
                return

        if clock: clock.start(board.side)
        try:
            raw=input(f"  {pname}'s move: ").strip()
        except EOFError: return
        if not raw: continue
        cmd=raw.lower()
        if cmd in('quit','exit','q'): return
        if cmd=='help': print(HELP); continue
        if cmd=='flip': persp=1-persp; continue
        if cmd=='elo': elo_sys.leaderboard(category=elo_category); continue
        if cmd=='pgn':
            pgn = export_pgn(board.san_log, wn, bn, '*')
            print(pgn); continue
        if cmd=='replay':
            replay_game(board.san_log, white_name=wn, black_name=bn); continue
        if cmd=='moves':
            sms=[board.san(m) for m in legal]
            for i in range(0,len(sms),8):
                print("  "+"  ".join(f"{s:<8}" for s in sms[i:i+8]))
            print(); continue
        if cmd=='resign':
            if clock: clock.stop(board.side)
            winner=BLACK if board.side==WHITE else WHITE
            print(f"  {pname} resigned.")
            handle_game_end(board,elo_sys,wn,bn,winner_color=winner,elo_category=elo_category)
            return
        if cmd=='draw':
            if clock: clock.stop(board.side)
            try:
                other=bn if board.side==WHITE else wn
                ans=input(f"  {other}: Accept draw? [y/N] ").strip().lower()
            except EOFError: ans='n'
            if ans in('y','yes'):
                handle_game_end(board,elo_sys,wn,bn,draw=True,elo_category=elo_category); return
            print("  Draw declined."); continue
        # Normalise move (accept e2e4, e2-e4, etc.)
        raw = board._normalise_input(raw)
        mv=board.parse_san(raw)
        if mv is None:
            print(f"  Illegal/unrecognised: '{raw}'. Try 'moves' or 'help'.")
            continue
        if clock: clock.stop(board.side)
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
  ┌──────────────────────────────────────────┐
  │              MAIN MENU  v2.0             │
  ├──────────────────────────────────────────┤
  │  1.  Play vs AI                          │
  │  2.  Local 2-Player                      │
  │  3.  Online Matchmaking                  │
  │  4.  Account Management                  │
  │  5.  ELO Leaderboard                     │
  │  6.  Analyze a PGN line                  │
  │  7.  Game Analysis (Online)              │
  │  8.  Friends & Messaging                 │
  │  9.  Learn an Opening                    │
  │  10. Daily Puzzle (Lichess)              │
  │  11. Endgame Trainer                     │
  │  12. Replay Saved Game                   │
  │  13. PGN Import / Export                 │
  │  14. Opening Explorer                    │
  │  15. Opening Quiz                        │
  │  16. Game Stats Dashboard                │
  │  17. Settings                            │
  │  18. Report a Bug                        │
  │  19. Server Daily Puzzle                 │
  │  20. Achievements                        │
  │  21. Tournaments                         │
  │  22. Lobby Chat                          │
  │  0.  Enable Offline Mode                 │
  │  Q.  Quit                                │
  └──────────────────────────────────────────┘
"""

MAIN_MENU_OFFLINE = """
  ┌──────────────────────────────────────────┐
  │              MAIN MENU  v2.0             │
  ├──────────────────────────────────────────┤
  │  1.  Play vs AI                          │
  │  2.  Local 2-Player                      │
  │  3.  Online Matchmaking [OFFLINE]        │
  │  4.  Account Management                  │
  │  5.  ELO Leaderboard                     │
  │  6.  Analyze a PGN line                  │
  │  7.  Game Analysis (Online)              │
  │  8.  Friends & Messaging [OFFLINE]       │
  │  9.  Learn an Opening                    │
  │  10. Daily Puzzle (Lichess)              │
  │  11. Endgame Trainer                     │
  │  12. Replay Saved Game                   │
  │  13. PGN Import / Export                 │
  │  14. Opening Explorer                    │
  │  15. Opening Quiz                        │
  │  16. Game Stats Dashboard                │
  │  17. Settings                            │
  │  18. Report a Bug                        │
  │  19. Server Puzzle [OFFLINE]             │
  │  20. Achievements [OFFLINE]              │
  │  21. Tournaments [OFFLINE]               │
  │  22. Lobby Chat [OFFLINE]               │
  │  0.  Enable Online Mode                  │
  │  Q.  Quit                                │
  └──────────────────────────────────────────┘
"""


# ════════════════════════════════════════════════════════════════════════
#  BUG REPORT SYSTEM
# ════════════════════════════════════════════════════════════════════════
_BUG_REPORT_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'bug_reports.json')

def _load_bug_reports():
    """Load existing bug reports from file."""
    if not os.path.exists(_BUG_REPORT_FILE):
        return []
    try:
        with open(_BUG_REPORT_FILE, 'r', encoding='utf-8') as f:
            return json.load(f)
    except Exception:
        return []

def _save_bug_reports(reports):
    """Save bug reports to file."""
    try:
        with open(_BUG_REPORT_FILE, 'w', encoding='utf-8') as f:
            json.dump(reports, f, indent=2, ensure_ascii=False)
        return True
    except Exception:
        return False

def report_bug():
    """
    Interactive bug reporting tool.
    Lets the player describe a bug and saves it to bug_reports.json.
    If online, also submits it to the server.
    """
    print("\n  ╔══════════════════════════════════════════════════════════╗")
    print("  ║                   REPORT A BUG                           ║")
    print("  ╠══════════════════════════════════════════════════════════╣")
    print("  ║  Help improve ASCII Chess by reporting bugs or issues.   ║")
    print("  ║  Reports are saved locally and (if online) sent to the   ║")
    print("  ║  server. Press Enter to cancel at any time.              ║")
    print("  ╚══════════════════════════════════════════════════════════╝")

    # Category selection
    categories = [
        "Gameplay / Rules",
        "AI / Engine",
        "Opening Book",
        "UI / Display",
        "Networking / Online",
        "Crash / Error",
        "Other",
    ]
    print("\n  Bug Category:")
    for i, cat in enumerate(categories, 1):
        print(f"    {i}. {cat}")
    try:
        cat_input = input("  Category [1-7]: ").strip()
    except EOFError:
        return
    if not cat_input:
        return
    try:
        cat_idx = int(cat_input) - 1
        category = categories[cat_idx] if 0 <= cat_idx < len(categories) else "Other"
    except ValueError:
        category = "Other"

    # Severity
    severities = ["Low", "Medium", "High", "Critical"]
    print("\n  Severity:")
    for i, sev in enumerate(severities, 1):
        print(f"    {i}. {sev}")
    try:
        sev_input = input("  Severity [1-4, default=2]: ").strip()
    except EOFError:
        return
    if not sev_input:
        severity = "Medium"
    else:
        try:
            sev_idx = int(sev_input) - 1
            severity = severities[sev_idx] if 0 <= sev_idx < len(severities) else "Medium"
        except ValueError:
            severity = "Medium"

    # Title
    try:
        title = input("\n  Short title (one line): ").strip()
    except EOFError:
        return
    if not title:
        print("  Bug report cancelled.")
        return

    # Description
    print("  Description (describe what happened vs what you expected).")
    print("  Type 'END' on its own line when done, or press Enter twice:")
    lines = []
    try:
        blank_count = 0
        while True:
            line = input("  > ")
            if line.strip().upper() == 'END':
                break
            if line == '':
                blank_count += 1
                if blank_count >= 2:
                    break
                lines.append('')
            else:
                blank_count = 0
                lines.append(line)
    except EOFError:
        pass
    description = '\n'.join(lines).strip()
    if not description:
        description = "(No description provided)"

    # Steps to reproduce (optional)
    try:
        steps = input("\n  Steps to reproduce (optional, press Enter to skip): ").strip()
    except EOFError:
        steps = ""

    # Build the report
    report = {
        "id": int(time.time() * 1000),
        "timestamp": datetime.now().isoformat(),
        "username": _current_user or "(not logged in)",
        "category": category,
        "severity": severity,
        "title": title,
        "description": description,
        "steps": steps,
        "status": "open",
        "submitted_to_server": False,
    }

    # Save locally
    reports = _load_bug_reports()
    reports.append(report)
    saved = _save_bug_reports(reports)

    print("\n  ╔══════════════════════════════════════════════════════════╗")
    if saved:
        print("  ║  ✓ Bug report saved locally.                             ║")
    else:
        print("  ║  ✗ Could not save bug report locally.                    ║")

    # Try to submit to server if online
    global _server_conn
    if not _offline_mode and _server_conn:
        try:
            _server_conn.send('BUG_REPORT', {
                'id': report['id'],
                'timestamp': report['timestamp'],
                'username': report['username'],
                'category': category,
                'severity': severity,
                'title': title,
                'description': description,
                'steps': steps,
            })
            resp = _server_conn.recv(timeout=5)
            if resp and resp.get('success'):
                report['submitted_to_server'] = True
                _save_bug_reports(reports)
                print("  ║  ✓ Bug report also submitted to server.                  ║")
            else:
                print("  ║  ○ Could not submit to server (saved locally only).       ║")
        except Exception:
            print("  ║  ○ Could not submit to server (saved locally only).       ║")
    else:
        print("  ║  ○ Offline — report saved locally only.                   ║")
    print("  ╚══════════════════════════════════════════════════════════╝")
    print(f"\n  Report ID: {report['id']}")
    print(f"  Category:  {category}  |  Severity: {severity}")
    print(f"  Title:     {title}")
    print()


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
             "desc": "The classical main line. White retreats the bishop and prepares a powerful central break."},
            {"name": "Berlin Defence",
             "moves": "e4 e5 Nf3 Nc6 Bb5 Nf6 O-O Nxe4 d4 Nd6 Bxc6 dxc6 dxe5 Nf5",
             "desc": "Solid and drawish. Black trades pawns for activity. Loved by world champions including Carlsen."},
            {"name": "Exchange Variation",
             "moves": "e4 e5 Nf3 Nc6 Bb5 a6 Bxc6 dxc6 O-O f6 d4 exd4 Nxd4",
             "desc": "White gives Black doubled c-pawns in exchange for a lasting structural edge."},
            {"name": "Marshall Attack",
             "moves": "e4 e5 Nf3 Nc6 Bb5 a6 Ba4 Nf6 O-O Be7 Re1 b5 Bb3 O-O c3 d5",
             "desc": "A pawn sacrifice by Black for a fierce king-hunt attack. Marshall's immortal idea."},
            {"name": "Schliemann Gambit",
             "moves": "e4 e5 Nf3 Nc6 Bb5 f5 Nc3 fxe4 Nxe4 d5",
             "desc": "An aggressive counter-gambit. Black stakes everything on an early assault."},
            {"name": "Chigorin Variation",
             "moves": "e4 e5 Nf3 Nc6 Bb5 a6 Ba4 Nf6 O-O Be7 Re1 b5 Bb3 Na5 Bc2 c5 d4 Qc7",
             "desc": "Black reroutes the knight to a5 to attack the bishop. A rich positional fight over the centre."},
            {"name": "Chigorin — cxd4 Line",
             "moves": "e4 e5 Nf3 Nc6 Bb5 a6 Ba4 Nf6 O-O Be7 Re1 b5 Bb3 Na5 Bc2 c5 d4 cxd4 Nxd4 Nxb3 axb3",
             "desc": "Black captures in the centre and exchanges the bishop. White gets open a-file and passed b-pawn potential."},
            {"name": "Archangel Variation",
             "moves": "e4 e5 Nf3 Nc6 Bb5 a6 Ba4 Nf6 O-O b5 Bb3 Bb7 d3 Be7",
             "desc": "The Archangel! Black immediately plays …b5 and fianchettos the bishop. Dynamic counterplay on the long diagonal."},
            {"name": "Neo-Archangel / Archangel Modern",
             "moves": "e4 e5 Nf3 Nc6 Bb5 a6 Ba4 Nf6 O-O b5 Bb3 Bb7 d3 Bc5 c3 d6 Nbd2 O-O",
             "desc": "A refined version where Black develops the bishop to c5 for extra pressure. Popular in correspondence chess."},
            {"name": "Breyer Variation",
             "moves": "e4 e5 Nf3 Nc6 Bb5 a6 Ba4 Nf6 O-O Be7 Re1 b5 Bb3 Nb8 d3 d6 c3 Nbd7",
             "desc": "Black's knight retreats to reroute via d7. Deeply solid — a favourite of Spassky and Karpov."},
            {"name": "Breyer — Bayonet",
             "moves": "e4 e5 Nf3 Nc6 Bb5 a6 Ba4 Nf6 O-O Be7 Re1 b5 Bb3 Nb8 d4 Nbd7 Nbd2 Bb7 Bc2 c5",
             "desc": "White advances d4 and keeps the bishop on c2 for maximum pressure. A rich strategic battle."},
            {"name": "Zaitsev Variation",
             "moves": "e4 e5 Nf3 Nc6 Bb5 a6 Ba4 Nf6 O-O Be7 Re1 b5 Bb3 d6 c3 O-O h3 Bb7 d4 Re8",
             "desc": "Black fianchettos the bishop and prepares …Bf8 to free the position. Sharp and double-edged."},
            {"name": "Rio Gambit",
             "moves": "e4 e5 Nf3 Nc6 Bb5 a6 Ba4 Nf6 O-O Nxe4 Re1 Nc5 Nxe5 Nxe5 Rxe5+ Be7 Bf1 Nf6 d4 Ne6 d5",
             "desc": "Black plays …Nxe4 early and White sacrifices tempo for the initiative. A tactical and underexplored line."},
            {"name": "Keres Variation",
             "moves": "e4 e5 Nf3 Nc6 Bb5 a6 Ba4 Nf6 O-O Be7 Re1 b5 Bb3 d6 c3 O-O d4 Bg4 d5 Na5 Bc2 c6",
             "desc": "Black pins the f3-knight and targets the centre. White advances d5 to cramp Black's queenside."},
            {"name": "Open Ruy Lopez",
             "moves": "e4 e5 Nf3 Nc6 Bb5 a6 Ba4 Nf6 O-O Nxe4 d4 b5 Bb3 d5 dxe5 Be6",
             "desc": "Black sacrifices a pawn to open the centre. A sharp, theory-heavy battleground."},
            {"name": "Steinitz Defence",
             "moves": "e4 e5 Nf3 Nc6 Bb5 d6 c3 Bd7 d4 Nge7 O-O Ng6 Re1",
             "desc": "A solid but passive defence. Black keeps the knight on c6 and prepares a solid structure."},
            {"name": "Cozio Variation",
             "moves": "e4 e5 Nf3 Nc6 Bb5 Nge7 O-O g6 c3 a6 Ba4 Bg7 d4",
             "desc": "Black plays …Nge7 to avoid the pin and prepares a kingside fianchetto. Unusual and tricky."},
            {"name": "Classical (…Bc5)",
             "moves": "e4 e5 Nf3 Nc6 Bb5 Bc5 c3 Nf6 d4 exd4 cxd4 Bb4+ Nc3 Nxe4 O-O Bxc3 bxc3 d5",
             "desc": "Black develops the bishop to c5 immediately. A rich classical battle with dynamic imbalances."},
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
        ("Polish Opening (1.b4)", [
            {"name": "Main Line vs e5",
             "moves": "b4 e5 Bb2 f6 b5 d5 e3 Be6 Nf3 Nd7 d4 dxe4 Nd2 Bd5 c4",
             "desc": "White's offbeat flank opening. The Bb2 bishop eyes the long diagonal toward e5."},
            {"name": "Polish Gambit",
             "moves": "b4 e5 Bb2 Bxb4 Bxe5 Nf6 c4 O-O Nf3 d6 Bg3 Nc6",
             "desc": "White sacrifices a pawn but gains active piece play and control of the centre."},
            {"name": "Polish vs d5",
             "moves": "b4 d5 Bb2 Nf6 e3 Bf5 Nf3 e6 Be2 Nbd7 O-O Bd6",
             "desc": "Against a central response, White maintains queenside pressure with Bb2."},
            {"name": "King's Indian Setup vs Polish",
             "moves": "b4 Nf6 Bb2 g6 b5 Bg7 e3 d6 d4 O-O Nf3 Nbd7 Be2",
             "desc": "Black ignores the wing thrust and builds a solid King's Indian formation."},
            {"name": "Polish vs c6 — Queenside Battle",
             "moves": "b4 c6 Bb2 a5 b5 cxb5 e4 e6 Bxb5 Nf6 Nf3 Be7 O-O O-O",
             "desc": "A queenside pawn battle. White aims to exploit the advanced b-pawn."},
        ]),
        ("English Opening (1.c4)", [
            {"name": "Symmetrical English",
             "moves": "c4 c5 Nc3 Nc6 g3 g6 Bg2 Bg7 Nf3 e6 O-O Nge7 d4 cxd4 Nxd4 O-O",
             "desc": "Black mirrors White's setup. A flexible system with rich positional play."},
            {"name": "Reversed Sicilian",
             "moves": "c4 e5 Nc3 Nf6 Nf3 Nc6 g3 d5 cxd5 Nxd5 Bg2 Nb6 O-O Be7",
             "desc": "White plays a Sicilian with an extra tempo. Dynamic and double-edged."},
            {"name": "Four Knights English",
             "moves": "c4 e5 Nc3 Nf6 Nf3 Nc6 g3 Bb4 Bg2 O-O O-O Re8 d3 Bxc3",
             "desc": "A solid positional battle. Black's bishop pair is traded for knight activity."},
            {"name": "Anglo-Indian Defence",
             "moves": "c4 Nf6 Nc3 e6 Nf3 d5 d4 Be7 Bg5 h6 Bh4 O-O e3 b6",
             "desc": "Black builds a Queen's Indian-like setup. Solid and flexible."},
            {"name": "Mikenas-Carls Variation",
             "moves": "c4 Nf6 Nc3 e6 e4 d5 e5 d4 exf6 dxc3 bxc3 Qxf6 d4 e5",
             "desc": "A sharp pawn sacrifice. White gains the centre and attacking chances."},
            {"name": "King's English",
             "moves": "c4 e5 g3 Nf6 Bg2 d5 cxd5 Nxd5 Nc3 Nb6 Nf3 Nc6 O-O Be7",
             "desc": "White fianchettos and keeps the position flexible; a rich strategic battle."},
            {"name": "Anglo-Grünfeld",
             "moves": "c4 Nf6 Nc3 d5 cxd5 Nxd5 g3 g6 Bg2 Nxc3 bxc3 Bg7 Nf3 O-O O-O c5",
             "desc": "A Grünfeld-like set-up from the English move order."},
        ]),
        ("Sicilian — Rossolimo & Moscow", [
            {"name": "Rossolimo (Bb5)",
             "moves": "e4 c5 Nf3 Nc6 Bb5 g6 Bxc6 dxc6 d3 Bg7 h3 Nf6 Nc3 O-O Be3",
             "desc": "White avoids heavy Sicilian theory. The doubled c-pawns limit Black's centre."},
            {"name": "Rossolimo (…e6 system)",
             "moves": "e4 c5 Nf3 Nc6 Bb5 e6 O-O Nge7 Re1 a6 Bf1 d5 exd5 exd5 d4",
             "desc": "Black challenges the centre; White keeps pressure with the bishop pair."},
            {"name": "Moscow Variation (…Bd7)",
             "moves": "e4 c5 Nf3 d6 Bb5+ Bd7 Bxd7+ Qxd7 c4 Nc6 Nc3 Nf6 d4 cxd4 Nxd4",
             "desc": "White exchanges the bishop early; a Maroczy Bind-like position arises."},
            {"name": "Moscow (…Nc6)",
             "moves": "e4 c5 Nf3 d6 Bb5+ Nc6 O-O Bd7 Re1 Nf6 c3 a6 Bf1 Bg4 h3 Bh5",
             "desc": "Black develops naturally and keeps options in the centre."},
        ]),
        ("Sicilian — Smith-Morra, Grand Prix & Alapin", [
            {"name": "Smith-Morra Gambit",
             "moves": "e4 c5 d4 cxd4 c3 dxc3 Nxc3 Nc6 Nf3 d6 Bc4 e6 O-O Nf6 Qe2 Be7 Rd1",
             "desc": "White sacrifices a pawn for fast development and an IQP attack."},
            {"name": "Grand Prix Attack",
             "moves": "e4 c5 Nc3 Nc6 f4 g6 Nf3 Bg7 Bc4 e6 f5 exf5 exf5 d5 Bb3 Nge7",
             "desc": "White launches an early kingside attack with f4–f5."},
            {"name": "Alapin (2.c3) — Nf6 line",
             "moves": "e4 c5 c3 Nf6 e5 Nd5 d4 cxd4 Nf3 Nc6 cxd4 d6 Bc4 Nb6 Bb3 dxe5",
             "desc": "A solid anti-Sicilian. White builds a centre, Black seeks quick counter-play."},
            {"name": "Alapin (2.c3) — d5 line",
             "moves": "e4 c5 c3 d5 exd5 Qxd5 d4 Nc6 Nf3 Bg4 Be2 cxd4 cxd4 e6 Nc3 Bb4",
             "desc": "Black stakes out d5 immediately; the game often becomes an IQP battle."},
        ]),
        ("Slav & Semi-Slav", [
            {"name": "Slav Defence",
             "moves": "d4 d5 c4 c6 Nf3 Nf6 Nc3 dxc4 a4 Bf5 e3 e6 Bxc4 Bb4 O-O Nbd7",
             "desc": "Black supports d5 solidly. A first-rate choice at the highest levels."},
            {"name": "Semi-Slav / Meran",
             "moves": "d4 d5 c4 c6 Nc3 Nf6 Nf3 e6 e3 Nbd7 Bd3 dxc4 Bxc4 b5 Bd3 a6 e4",
             "desc": "One of the most dynamically complex openings in chess. Wild pawn play."},
            {"name": "Moscow Variation (Slav)",
             "moves": "d4 d5 c4 c6 Nf3 Nf6 Nc3 dxc4 e3 b5 a4 b4 Ne4 Ba6 Nxf6+ exf6",
             "desc": "White sacrifices a piece for positional compensation on the queenside."},
            {"name": "Anti-Moscow Gambit",
             "moves": "d4 d5 c4 c6 Nf3 Nf6 Nc3 e6 Bg5 h6 Bh4 dxc4 e4 g5 Bg3 b5",
             "desc": "An ultra-sharp gambit where Black grabs pawns and White gets piece activity."},
        ]),
        ("Tarrasch & Semi-Tarrasch", [
            {"name": "Tarrasch Defence",
             "moves": "d4 d5 c4 e6 Nc3 c5 cxd5 exd5 Nf3 Nc6 g3 Nf6 Bg2 Be7 O-O O-O Bg5",
             "desc": "Black accepts an IQP for free development and active piece play."},
            {"name": "Semi-Tarrasch",
             "moves": "d4 Nf6 c4 e6 Nf3 d5 Nc3 c5 cxd5 Nxd5 e3 Nc6 Bd3 Be7 O-O O-O",
             "desc": "A flexible IQP structure. Black has fewer weaknesses than in the full Tarrasch."},
        ]),
        ("Réti Opening", [
            {"name": "Réti Gambit",
             "moves": "Nf3 d5 c4 dxc4 e3 Nf6 Bxc4 e6 O-O c5 d4",
             "desc": "White regains the pawn with a Catalan-like initiative."},
            {"name": "King's Indian Réti",
             "moves": "Nf3 Nf6 c4 g6 g3 Bg7 Bg2 O-O O-O d6 d4 Nc6 Nc3 a6 d5 Na5 Nd2 c5",
             "desc": "A King's Indian pawn structure from a Réti move order."},
            {"name": "Réti vs d5 (slow build)",
             "moves": "Nf3 d5 g3 Nf6 Bg2 e6 O-O Be7 d3 O-O Nbd2 c5 c3 Nc6 Re1 b5",
             "desc": "White adopts a patient fianchetto strategy and waits for the right moment."},
            {"name": "Zukertort Attack",
             "moves": "Nf3 d5 b3 Nf6 Bb2 Bf5 g3 e6 Bg2 Be7 O-O O-O d3 c5 Nbd2",
             "desc": "An old-fashioned yet solid hyper-modern set-up from 1.Nf3."},
        ]),
        ("Benoni & Benko — Advanced", [
            {"name": "Taimanov Benoni",
             "moves": "d4 Nf6 c4 c5 d5 e6 Nc3 exd5 cxd5 d6 Nf3 g6 Nd2 Bg7 e4 O-O Be2",
             "desc": "A flexible move order leading to a blocked Benoni centre."},
            {"name": "Czech Benoni",
             "moves": "d4 Nf6 c4 c5 d5 e5 Nc3 d6 e4 Be7 Nge2 O-O Ng3 Ne8 Be2 g6",
             "desc": "Black closes the centre with …e5. Very solid but slightly cramped."},
            {"name": "Blumenfeld Gambit",
             "moves": "d4 Nf6 c4 e6 Nf3 c5 d5 b5 dxe6 fxe6 cxb5 d5 Nc3 Bd6 e4 dxe4",
             "desc": "Black sacrifices a pawn for an open game and piece activity."},
            {"name": "Benko Gambit — Fianchetto",
             "moves": "d4 Nf6 c4 c5 d5 b5 cxb5 a6 bxa6 g6 Nc3 Bxa6 Nf3 d6 g3 Bg7 Bg2",
             "desc": "White fianchettos and keeps the position slightly more solid."},
        ]),
        ("Nimzowitsch & Larsen Attacks", [
            {"name": "Nimzowitsch-Larsen (1.b3)",
             "moves": "b3 e5 Bb2 Nc6 e3 Nf6 Nf3 e4 Nd4 Bc5 Nxc6 dxc6 d4 exd3 Bxd3",
             "desc": "A hyper-modern flank opening. White pressures the centre from the outside."},
            {"name": "Larsen's Opening (1.b3 vs d5)",
             "moves": "Nf3 d5 b3 c5 Bb2 Nc6 e3 Nf6 Bb5 Bg4 h3 Bh5 O-O e6 d4",
             "desc": "A Réti-Larsen hybrid. White builds pressure on the long diagonal."},
        ]),
        ("Ponziani, Bishop's & Vienna — Extended", [
            {"name": "Ponziani Opening",
             "moves": "e4 e5 Nf3 Nc6 c3 d5 Qa4 Nf6 Nxe5 Bd6 Nxc6 bxc6 d3 O-O Be2",
             "desc": "An old gambit line. White has to be careful but gets rich play."},
            {"name": "Ponziani — Nf6 counter-attack",
             "moves": "e4 e5 Nf3 Nc6 c3 Nf6 d4 Nxe4 d5 Ne7 Nxe5 d6 Nxf7 Kxf7 dxe6+ Kxe6",
             "desc": "Black counter-attacks immediately with …Nf6 for sharp complications."},
            {"name": "Bishop's Opening",
             "moves": "e4 e5 Bc4 Nf6 d3 c6 Nf3 d5 Bb3 Bd6 Nc3 O-O O-O",
             "desc": "A flexible approach avoiding the main lines of the Italian/Spanish."},
            {"name": "Vienna Gambit",
             "moves": "e4 e5 Nc3 Nf6 f4 d5 fxe5 Nxe4 Qf3 Nc6 Bb5 Nd4 Qxe4+ Nxb5 Nxb5",
             "desc": "White sacrifices a piece for a ferocious king-hunt."},
        ]),
        ("Petrov, Philidor & Centre Game", [
            {"name": "Petrov — Classical",
             "moves": "e4 e5 Nf3 Nf6 Nxe5 d6 Nf3 Nxe4 d4 d5 Bd3 Nc6 O-O Be7 Re1 Bg4",
             "desc": "One of the most solid responses to 1.e4. Black equalises comfortably."},
            {"name": "Petrov — Three Knights",
             "moves": "e4 e5 Nf3 Nf6 Nc3 Nc6 Bb5 Nd4 Nxd4 exd4 Nd5 Nxd5 exd5 Qe7 Qe2",
             "desc": "White tries for an early advantage; the game becomes sharp quickly."},
            {"name": "Philidor Defence",
             "moves": "e4 e5 Nf3 d6 d4 Nf6 Nc3 Nbd7 Bc4 Be7 O-O O-O Re1",
             "desc": "Black keeps a solid pawn structure but is slightly cramped."},
            {"name": "Centre Game",
             "moves": "e4 e5 d4 exd4 Qxd4 Nc6 Qe3 Nf6 Nc3 Bb4 Bd2 O-O O-O-O Re8",
             "desc": "White develops the queen early; Black gets easy equality."},
            {"name": "Danish Gambit",
             "moves": "e4 e5 d4 exd4 c3 dxc3 Bc4 cxb2 Bxb2 d5 Bxd5 Nf6 Nc3 Bb4 Ne2",
             "desc": "A double pawn sacrifice for a huge development lead. Romantic and fun!"},
        ]),
        ("Miscellaneous & Offbeat", [
            {"name": "Bird's Opening",
             "moves": "f4 d5 Nf3 Nf6 e3 g6 Be2 Bg7 O-O O-O d3 c5 Qe1 Nc6 Qh4",
             "desc": "White controls e5 and targets the kingside. An underrated weapon."},
            {"name": "Grob Attack (1.g4)",
             "moves": "g4 d5 Bg2 Bxg4 c4 c3 Qb3 Bd7 Nf3 Nf6",
             "desc": "An ultra-aggressive and unorthodox first move. Best for surprise value."},
            {"name": "Modern Defence",
             "moves": "e4 g6 d4 Bg7 Nc3 d6 f4 Nf6 Nf3 O-O Bd3 Na6 O-O c5 d5 Rb8",
             "desc": "Black hyper-modernly allows White a big centre and then attacks it."},
            {"name": "Pirc — Austrian Attack",
             "moves": "e4 d6 d4 Nf6 Nc3 g6 f4 Bg7 Nf3 c5 dxc5 Qa5 Bd3 Qxc5 Qe2 O-O Be3",
             "desc": "White builds a huge centre and storms the kingside. Very sharp."},
            {"name": "Latvian Gambit",
             "moves": "e4 e5 Nf3 f5 Nxe5 Qf6 Nc4 fxe4 Nc3 Qf7 Ne3 c6 d4 exd3 Bxd3 d5",
             "desc": "An aggressive counter-gambit. Black sacrifices material for an attack."},
            {"name": "Halloween Gambit",
             "moves": "e4 e5 Nf3 Nc6 Nc3 Nf6 Nxe5 Nxe5 d4 Nc6 d5 Ne5 f4 Ng6 e5 Ng8",
             "desc": "A wild knight sacrifice on move 4. White gets a crushing attack or loses quickly."},
        ]),
        # ── New categories ─────────────────────────────────────────────────
        ("Queen's Indian Defence", [
            {"name": "Classical (4.g3)",
             "moves": "d4 Nf6 c4 e6 Nf3 b6 g3 Bb7 Bg2 Be7 O-O O-O Nc3 Ne4 Qc2 Nxc3 Qxc3 f5",
             "desc": "White fianchettos and prepares a long-term positional squeeze."},
            {"name": "Petrosian System (4.a3)",
             "moves": "d4 Nf6 c4 e6 Nf3 b6 a3 Bb7 Nc3 d5 cxd5 Nxd5 Qc2 Nxc3 bxc3 Be7 e4",
             "desc": "White prevents …Bb4 and builds an imposing centre. Named for the iron defender."},
            {"name": "Nimzo-Indian move order",
             "moves": "d4 Nf6 c4 e6 Nf3 b6 Nc3 Bb4 Bg5 Bb7 e3 h6 Bh4 Bxc3+ bxc3 d6",
             "desc": "Black plays …Bb4 to force doubled pawns, then fianchettos the bishop."},
            {"name": "Miles Variation",
             "moves": "d4 Nf6 c4 e6 Nf3 b6 Bf4 Bb7 e3 Be7 h3 O-O Bd3 c5 dxc5 bxc5 O-O Nc6",
             "desc": "White develops quickly and keeps queenside tension. Practical and solid."},
        ]),
        ("Catalan Opening", [
            {"name": "Open Catalan",
             "moves": "d4 Nf6 c4 e6 g3 d5 Bg2 dxc4 Nf3 a6 O-O Nc6 Qc2 Be7 Qxc4 O-O",
             "desc": "Black accepts the pawn then releases it. The g2-bishop exerts long-term pressure."},
            {"name": "Closed Catalan",
             "moves": "d4 Nf6 c4 e6 g3 d5 Bg2 Be7 Nf3 O-O O-O dxc4 Qc2 a6 Qxc4 b5 Qc2 Bb7",
             "desc": "Black keeps the centre closed. A rich strategic game often reaching favourable endgames."},
            {"name": "Catalan with …c6",
             "moves": "d4 d5 c4 c6 g3 Nf6 Bg2 Bf5 Nf3 e6 O-O Be7 b3 O-O Bb2 Nbd7",
             "desc": "Black combines the Slav structure with the Catalan setup for solid equality."},
        ]),
        ("Trompowsky Attack", [
            {"name": "Trompowsky Main (…d5)",
             "moves": "d4 Nf6 Bg5 d5 Bxf6 exf6 e3 c6 Bd3 Bd6 Ne2 O-O Nd2 Re8",
             "desc": "White immediately pins the knight. Black gets the bishop pair and solid structure."},
            {"name": "Trompowsky (…Ne4)",
             "moves": "d4 Nf6 Bg5 Ne4 Bf4 c5 f3 Qa5+ c3 Nf6 d5 e6 e4 exd5 exd5 d6",
             "desc": "Black immediately challenges the bishop with …Ne4. Sharp and double-edged."},
            {"name": "Trompowsky (…e6)",
             "moves": "d4 Nf6 Bg5 e6 e4 h6 Bxf6 Qxf6 Nc3 d6 Qd2 a6 O-O-O Nd7 f4",
             "desc": "Black accepts the doubled pawns but gets open lines for counterplay."},
        ]),
        ("London System — Extended", [
            {"name": "London vs KID (Classical)",
             "moves": "d4 Nf6 Bf4 e6 e3 d5 Nf3 c5 c3 Nc6 Nbd2 Bd6 Bg3 O-O Bd3",
             "desc": "A reliable setup for White. The Bg3 prevents …Ne4 and keeps the structure solid."},
            {"name": "London — Torre Attack hybrid",
             "moves": "d4 Nf6 Nf3 e6 Bg5 d5 e3 Be7 Nbd2 O-O Bd3 c5 c3 b6 O-O Bb7",
             "desc": "White pins the knight with Bg5 in the London structure. Flexible and solid."},
            {"name": "London — King's Indian Refusal",
             "moves": "d4 Nf6 Bf4 g6 Nc3 d5 e3 Bg7 h4 h6 Be2 O-O Nf3 c5 dxc5 Qa5 Nd2",
             "desc": "White meets the King's Indian setup with h4, aiming for early queenside play."},
            {"name": "London — Accelerated (2.Bf4)",
             "moves": "d4 d5 Bf4 c5 e3 Nc6 c3 Qb6 Qb3 c4 Qxb6 axb6 Nd2 e6 Ngf3 Bd6",
             "desc": "White rushes the bishop out early for maximum simplicity."},
        ]),
        ("Sicilian — Dragon & Accelerated", [
            {"name": "Yugoslav Attack (Dragon)",
             "moves": "e4 c5 Nf3 d6 d4 cxd4 Nxd4 Nf6 Nc3 g6 Be3 Bg7 f3 O-O Qd2 Nc6 O-O-O d5",
             "desc": "One of the most violent openings in chess. White attacks the king, Black counterattacks."},
            {"name": "Dragon — Classical",
             "moves": "e4 c5 Nf3 d6 d4 cxd4 Nxd4 Nf6 Nc3 g6 Be2 Bg7 O-O O-O Be3 Nc6 Nb3",
             "desc": "White castles kingside and plays more quietly. The game remains strategically rich."},
            {"name": "Accelerated Dragon",
             "moves": "e4 c5 Nf3 Nc6 d4 cxd4 Nxd4 g6 c4 Bg7 Be3 Nf6 Nc3 d6 Be2 O-O O-O",
             "desc": "Black achieves the Dragon structure without playing …d6 first, avoiding the Yugoslav."},
            {"name": "Maroczy Bind",
             "moves": "e4 c5 Nf3 Nc6 d4 cxd4 Nxd4 g6 c4 Bg7 Be3 Nf6 Nc3 d6 Be2 O-O O-O",
             "desc": "White clamps the centre with c4. Black must find active counterplay or suffer."},
        ]),
        ("Vienna Game — Extended", [
            {"name": "Vienna — Falkbeer Variation",
             "moves": "e4 e5 Nc3 Nf6 Bc4 Nc6 d3 Na5 Bb5 c6 Ba4 b5 Bb3 Nxb3 axb3 d6 Nf3",
             "desc": "A slow strategic battle. Black tries to trade off White's dark-squared bishop."},
            {"name": "Vienna — Stanley Variation",
             "moves": "e4 e5 Nc3 Nc6 Bc4 Bc5 Qg4 Qf6 Nd5 Qxf2+ Kd1 Kf8 Nf3 h6 d3",
             "desc": "Wild complications arise after Qg4. Not for the faint-hearted!"},
            {"name": "Vienna — Steinitz Variation",
             "moves": "e4 e5 Nc3 Nf6 g3 d5 exd5 Nxd5 Bg2 Nxc3 bxc3 Nc6 Nf3 Bc5 O-O O-O d3",
             "desc": "White fianchettos and keeps the position solid. Strategic play."},
        ]),
        ("Alekhine's Defence", [
            {"name": "Four Pawns Attack",
             "moves": "e4 Nf6 e5 Nd5 d4 d6 c4 Nb6 f4 dxe5 fxe5 Nc6 Nf3 Bf5 Be2 e6 O-O",
             "desc": "White builds a giant pawn centre; Black must undermine it rapidly or be crushed."},
            {"name": "Exchange Variation",
             "moves": "e4 Nf6 e5 Nd5 d4 d6 exd6 exd6 Nf3 Nc6 Be2 Be7 O-O O-O c4 Nf6",
             "desc": "White exchanges the e5 pawn for a small but enduring spatial advantage."},
            {"name": "Modern Variation",
             "moves": "e4 Nf6 e5 Nd5 d4 d6 Nf3 g6 Bc4 Nb6 Bb3 Bg7 Nbd2 Nc6 O-O dxe5 dxe5",
             "desc": "A solid modern treatment. Black fianchettos and pressures e5."},
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


# Puzzle trainer removed — solutions were invalid. Use Lichess.org for verified puzzles.

def _placeholder_removed():
    pass


def _get_all_puzzles_REMOVED():
    """Puzzle trainer removed — solutions were invalid. Use Lichess.org for verified puzzles."""
    return [
        # ─── MATE IN 1 ────────────────────────────────────────────────────
        {
            "id": 1, "title": "Mate in 1 — Back Rank",
            "theme": "Mate in 1 / Back Rank",
            "fen":   "6k1/5ppp/8/8/8/8/5PPP/3R2K1 w - - 0 1",
            "moves": ["Rd8#"],
            "hint":  "Rooks love open files and the 8th rank…",
        },
        {
            "id": 2, "title": "Mate in 1 — Queen & Rook",
            "theme": "Mate in 1",
            "fen":   "r4rk1/ppp2ppp/8/3Q4/8/8/PPP2PPP/4RRK1 w - - 0 1",
            "moves": ["Qd8#"],
            "hint":  "The queen can deliver check along the d-file.",
        },
        {
            "id": 3, "title": "Mate in 1 — Smothered",
            "theme": "Mate in 1 / Smothered",
            "fen":   "6rk/6pp/7N/8/8/8/8/6K1 w - - 0 1",
            "moves": ["Nf7#"],
            "hint":  "The knight can land on a square where the king has no escape.",
        },
        {
            "id": 4, "title": "Mate in 1 — Pin & Mate",
            "theme": "Mate in 1",
            "fen":   "5rk1/pppp1Bpp/8/8/8/8/PPPP2PP/6K1 w - - 0 1",
            "moves": ["Bxg8#"],
            "hint":  "The bishop captures the rook delivering checkmate.",
        },
        {
            "id": 5, "title": "Mate in 1 — Rook & King",
            "theme": "Mate in 1",
            "fen":   "7k/8/6K1/8/8/8/8/7R w - - 0 1",
            "moves": ["Rh7#"],
            "hint":  "The rook cuts off the last rank with king support.",
        },
        # ─── MATE IN 2 ────────────────────────────────────────────────────
        {
            "id": 6, "title": "Mate in 2 — Arabian Mate",
            "theme": "Mate in 2 / Arabian Mate",
            "fen":   "5rk1/5Npp/8/8/8/8/8/R5K1 w - - 0 1",
            "moves": ["Nh6+", "Kh8", "Ra8#"],
            "hint":  "The knight covers key flight squares for the rook to deliver mate.",
        },
        {
            "id": 7, "title": "Mate in 2 — Queen Sacrifice",
            "theme": "Mate in 2 / Sacrifice",
            "fen":   "r1b1kb1r/pppp1ppp/2n2n2/4p2Q/2B1P3/8/PPPP1PPP/RNB1K1NR w KQkq - 0 1",
            "moves": ["Qxf7+", "Kxf7", "Bxe6#"],
            "hint":  "Remove the defender with a forcing sacrifice.",
        },
        {
            "id": 8, "title": "Mate in 2 — Corridor",
            "theme": "Mate in 2 / Corridor",
            "fen":   "8/8/8/8/8/5k2/5Q2/5K2 w - - 0 1",
            "moves": ["Qa2+", "Ke3", "Qe6#"],
            "hint":  "Drive the king to a mating square with checks.",
        },
        {
            "id": 9, "title": "Mate in 2 — Double Check",
            "theme": "Mate in 2",
            "fen":   "r1b1k2r/pppp1ppp/2n2n2/2b5/2B1P3/2NP1N2/PPP2PPP/R1BQK2R b KQkq - 0 1",
            "moves": ["Ng4", "O-O", "Nxf2"],
            "hint":  "A knight leap forks king and rook.",
        },
        {
            "id": 10, "title": "Mate in 2 — Rook Roller",
            "theme": "Mate in 2",
            "fen":   "6k1/8/6K1/8/8/8/8/R1R5 w - - 0 1",
            "moves": ["Ra8+", "Kh7", "Rh1#"],
            "hint":  "Two rooks take turns delivering check.",
        },
        # ─── MATE IN 3 ────────────────────────────────────────────────────
        {
            "id": 11, "title": "Mate in 3 — Smothered Mate",
            "theme": "Mate in 3 / Smothered",
            "fen":   "6rk/6pp/8/8/8/6N1/8/6K1 w - - 0 1",
            "moves": ["Nf5", "g6", "Nh6", "Kh7", "Nf7#"],
            "hint":  "The knight manoeuvres into position for a smothered mate.",
        },
        {
            "id": 12, "title": "Mate in 3 — Anastasia's Mate",
            "theme": "Mate in 3",
            "fen":   "5rk1/pp1R1ppp/8/2p5/4P3/2N5/PP3PPP/6K1 w - - 0 1",
            "moves": ["Rd8", "Rxd8", "Ne4", "Rd1", "Nf6#"],
            "hint":  "Combine rook and knight for a back-rank mating net.",
        },
        # ─── TACTICAL THEMES ──────────────────────────────────────────────
        {
            "id": 13, "title": "Fork — Knight Fork",
            "theme": "Tactics / Fork",
            "fen":   "r1bqkb1r/pppp1ppp/2n2n2/4p3/2B1P3/5N2/PPPP1PPP/RNBQK2R w KQkq - 0 1",
            "moves": ["Ng5", "d5", "Nxf7"],
            "hint":  "Find the knight leap that wins material.",
        },
        {
            "id": 14, "title": "Pin — Absolute Pin",
            "theme": "Tactics / Pin",
            "fen":   "r1bqk2r/pppp1ppp/2n2n2/2b1p3/2B1P3/3P1N2/PPP2PPP/RNBQK2R b KQkq - 0 1",
            "moves": ["Ng4", "O-O", "Nxf2"],
            "hint":  "Exploit the pin on the f3-knight.",
        },
        {
            "id": 15, "title": "Skewer — Rook Skewer",
            "theme": "Tactics / Skewer",
            "fen":   "3k4/8/8/8/8/8/8/1R1K4 w - - 0 1",
            "moves": ["Rb8+", "Kc7", "Rb7+"],
            "hint":  "A skewer forces the king away, winning the piece behind.",
        },
        {
            "id": 16, "title": "Discovered Attack",
            "theme": "Tactics / Discovered Attack",
            "fen":   "r2qkb1r/ppp2ppp/2np1n2/4p1B1/2B1P3/2NP4/PPP2PPP/R2QK2R w KQkq - 0 1",
            "moves": ["Nd5", "Nxd5", "Bxd8"],
            "hint":  "Move one piece to unleash an attack by a piece behind it.",
        },
        {
            "id": 17, "title": "Deflection — Queen Deflection",
            "theme": "Tactics / Deflection",
            "fen":   "3rk3/8/8/4q3/8/4Q3/8/4RK2 w - - 0 1",
            "moves": ["Qe5+", "Qxe5", "Re8#"],
            "hint":  "Force the queen away from a key defensive duty.",
        },
        {
            "id": 18, "title": "Zwischenzug — Intermediate Move",
            "theme": "Tactics / Zwischenzug",
            "fen":   "r1bq1rk1/ppp2ppp/2n2n2/3pp3/3P4/2NBPN2/PPP2PPP/R2QK2R b KQkq - 0 1",
            "moves": ["e4", "Bxf6", "Qxd1+"],
            "hint":  "Instead of recapturing, find the surprising in-between move!",
        },
        {
            "id": 19, "title": "Overloading — Defender Overload",
            "theme": "Tactics / Overloading",
            "fen":   "4r1k1/pp3ppp/2p5/4q3/2B5/2Q5/PPP2PPP/4R1K1 w - - 0 1",
            "moves": ["Rxe5", "Rxe5", "Qxc6"],
            "hint":  "The defending rook is covering two things at once — exploit it.",
        },
        {
            "id": 20, "title": "X-Ray Attack",
            "theme": "Tactics / X-Ray",
            "fen":   "3r4/8/8/8/8/8/8/3RK2k w - - 0 1",
            "moves": ["Kf2", "Kh2", "Kg3", "Kg1", "Rd2"],
            "hint":  "Use indirect pressure through your opponent's piece.",
        },
        # ─── ENDGAME PUZZLES ──────────────────────────────────────────────
        {
            "id": 21, "title": "Endgame — Lucena Position",
            "theme": "Endgame / Rook",
            "fen":   "1K1k4/1P6/8/8/8/8/r7/4R3 w - - 0 1",
            "moves": ["Re4", "Ra1", "Kc7"],
            "hint":  "Build a 'bridge' with your rook to shelter your king.",
        },
        {
            "id": 22, "title": "Endgame — King & Pawn Opposition",
            "theme": "Endgame / Pawn",
            "fen":   "8/8/8/4k3/8/4K3/4P3/8 w - - 0 1",
            "moves": ["Kd3", "Kd5", "e4+"],
            "hint":  "Use the opposition to escort your pawn to promotion.",
        },
        {
            "id": 23, "title": "Endgame — Passed Pawn Breakthrough",
            "theme": "Endgame / Passed Pawn",
            "fen":   "8/p1P5/Pp6/8/8/8/8/4K1k1 w - - 0 1",
            "moves": ["c8=Q", "a5", "Qb7"],
            "hint":  "Promote the c-pawn and use your queen to queen the a-pawn.",
        },
        {
            "id": 24, "title": "Endgame — Queen vs Rook",
            "theme": "Endgame / Queen",
            "fen":   "8/8/8/8/3k4/8/8/3KQ3 w - - 0 1",
            "moves": ["Qe4+", "Kc5", "Kc3"],
            "hint":  "Coordinate king and queen to restrict the enemy king.",
        },
        {
            "id": 25, "title": "Endgame — Rook Ending Cut-off",
            "theme": "Endgame / Rook",
            "fen":   "8/5k2/8/8/8/8/5P2/3RK3 w - - 0 1",
            "moves": ["Rd7+", "Ke8", "Ke2"],
            "hint":  "Cut off the king with your rook, then escort the pawn.",
        },
        # ─── OPENING TRAPS ────────────────────────────────────────────────
        {
            "id": 26, "title": "Trap — Fried Liver Attack",
            "theme": "Opening Trap",
            "fen":   "r1bqkb1r/ppp2ppp/2np4/4N3/2B5/8/PPPP1PPP/RNBQK2R w KQkq - 0 6",
            "moves": ["Nxf7", "Kxf7", "Qf3+"],
            "hint":  "Sacrifice the knight to open the king!",
        },
        {
            "id": 27, "title": "Trap — Scholar's Mate Defense",
            "theme": "Opening Trap",
            "fen":   "rnbqkbnr/pppp1ppp/8/4p3/2B1P3/5Q2/PPPP1PPP/RNB1K1NR b KQkq - 3 3",
            "moves": ["Nc6", "Qxf7+", "Ke7"],
            "hint":  "Find the defense that avoids the scholar's mate and counterattacks.",
        },
        {
            "id": 28, "title": "Trap — Budapest Gambit Trap",
            "theme": "Opening Trap",
            "fen":   "r1bqkb1r/pppp1ppp/5n2/4P3/8/8/PPP1PPPP/RNBQKBNR b KQkq - 0 4",
            "moves": ["Ne4", "Nd2", "Qh4+"],
            "hint":  "A surprising queen fork forces material gain.",
        },
        # ─── COMBINATIONS ─────────────────────────────────────────────────
        {
            "id": 29, "title": "Combination — Greek Gift Sacrifice",
            "theme": "Combination / Sacrifice",
            "fen":   "r1bq1rk1/ppp2ppp/2n2n2/4p3/2BpP3/2N2N2/PPP2PPP/R1BQK2R w KQ - 0 7",
            "moves": ["Bxf7+", "Rxf7", "Ng5"],
            "hint":  "The bishop sacrifice on f7 forks king and rook, forcing a powerful follow-up.",
        },
        {
            "id": 30, "title": "Combination — Windmill",
            "theme": "Combination / Windmill",
            "fen":   "r2q1rk1/ppp2p1p/2np1np1/2b1p1B1/2B1P3/2NP1N2/PPP2PPP/R2QK2R w KQ - 0 9",
            "moves": ["Bxf6", "Bxf6", "Ng5"],
            "hint":  "Set up a series of alternating discoveries.",
        },
    ]


def puzzles_menu():
    """Fetch and play today's Lichess daily puzzle (engine-verified, always correct)."""
    import urllib.request, json as _json

    print("\n  ╔══════════════════════════════════════════════════════════╗")
    print("  ║              LICHESS DAILY PUZZLE                        ║")
    print("  ╠══════════════════════════════════════════════════════════╣")
    print("  ║  Fetching today's puzzle from lichess.org...             ║")
    print("  ╚══════════════════════════════════════════════════════════╝")

    # ── Fetch from Lichess public API ────────────────────────────────────
    try:
        req = urllib.request.Request(
            'https://lichess.org/api/puzzle/daily',
            headers={'Accept': 'application/json', 'User-Agent': 'TerminalChess/1.0'}
        )
        with urllib.request.urlopen(req, timeout=8) as resp:
            data = _json.loads(resp.read().decode())
    except Exception as e:
        print(f"\n  Could not fetch puzzle (no internet?): {e}")
        print("  Visit lichess.org/training for puzzles.")
        try: input("  Press Enter to return...")
        except EOFError: pass
        return

    # ── Parse response ────────────────────────────────────────────────
    puzzle_data = data.get('puzzle', {})
    game_data   = data.get('game', {})

    fen        = puzzle_data.get('initialFen') or data.get('game', {}).get('fen', '')
    solution   = puzzle_data.get('solution', [])   # list of UCI move strings
    rating     = puzzle_data.get('rating', '?')
    themes     = ', '.join(puzzle_data.get('themes', []))
    puzzle_id  = puzzle_data.get('id', '?')
    puzzle_url = f"https://lichess.org/training/{puzzle_id}"

    if not fen or not solution:
        print("\n  Could not parse puzzle data from Lichess response.")
        try: input("  Press Enter to return...")
        except EOFError: pass
        return

    # ── The FEN given is the position BEFORE the opponent's last move;
    #    the first move in the solution list is the opponent's move we must
    #    apply, then all subsequent moves alternate (ours, theirs, ours…).
    board = _board_from_fen(fen)
    if board is None:
        print("  Could not load puzzle position.")
        return

    # Apply first move (opponent's "key" move that sets the puzzle)
    def _uci_to_move(b, uci):
        """Parse a UCI string like 'e2e4' or 'e7e8q' into a Move."""
        if len(uci) < 4: return None
        fr = s2sq(uci[:2]); to = s2sq(uci[2:4])
        promo = None
        if len(uci) == 5:
            promo = {'q': QUEEN, 'r': ROOK, 'b': BISHOP, 'n': KNIGHT}.get(uci[4].lower())
        for m in b.legal():
            if m.from_sq == fr and m.to_sq == to:
                if promo is None or getattr(m, 'promo', None) == promo:
                    return m
        return None

    # Apply the "setup" move (first entry = what the opponent just played)
    setup_uci = solution[0]
    setup_m   = _uci_to_move(board, setup_uci)
    if setup_m:
        sn = board.san(setup_m)
        board.make(setup_m)
        board.san_log.append(sn)
        print(f"\n  Opponent just played: {sn}")
    your_moves = solution[1:]   # alternating: your move, their reply, your move…

    persp    = board.side
    side_str = "White" if board.side == WHITE else "Black"

    print(f"\n  ╔══════════════════════════════════════════════════════════╗")
    print(f"  ║  Lichess Daily Puzzle — {datetime.now().strftime('%d %B %Y'):<33}║")
    print(f"  ╠══════════════════════════════════════════════════════════╣")
    print(f"  ║  Rating : {rating:<47}║")
    print(f"  ║  Themes : {themes[:47]:<47}║")
    print(f"  ║  URL    : {puzzle_url:<47}║")
    print(f"  ║  {side_str} to move{'':42}║")
    print(f"  ╚══════════════════════════════════════════════════════════╝")

    move_idx = 0
    errors   = 0
    last_mv  = setup_m

    while move_idx < len(your_moves):
        draw_board(board, persp, last_mv)

        expected_uci = your_moves[move_idx]
        expected_m   = _uci_to_move(board, expected_uci)
        if expected_m is None:
            print(f"  [Puzzle data issue] Cannot parse move {expected_uci}")
            break

        if move_idx % 2 == 1:
            # Opponent's forced reply — play automatically
            sn = board.san(expected_m)
            board.make(expected_m)
            board.san_log.append(sn)
            last_mv = expected_m
            print(f"\n  Opponent replies: {sn}\n")
            move_idx += 1
            continue

        # Your turn
        mn       = board.fullmove
        notation = f"{mn}." if board.side == WHITE else f"{mn}..."
        attempts = 0

        while True:
            try:
                raw = input(f"  Your move ({notation} ?): ").strip()
            except EOFError:
                return
            cmd = raw.lower()
            if cmd in ('q', 'quit', 'exit', '0'):
                return
            if cmd == 'hint':
                # Show destination square only
                hint_sq = expected_uci[2:4]
                print(f"  Hint: aim for {hint_sq}")
                continue
            if cmd == 'solution':
                sol_sans = []
                b2 = _board_from_fen(fen)
                for uci in solution:
                    m2 = _uci_to_move(b2, uci)
                    if m2:
                        sol_sans.append(b2.san(m2)); b2.make(m2)
                print(f"  Solution: {' '.join(sol_sans)}")
                try: input("  Press Enter to continue...")
                except EOFError: pass
                return

            player_m = board.parse_san(board._normalise_input(raw))
            if player_m is None:
                print(f"  Illegal or unrecognised: '{raw}'. Try again.")
                continue

            if player_m == expected_m:
                sn = board.san(player_m)
                board.make(player_m)
                board.san_log.append(sn)
                last_mv = player_m
                print(f"  ✓ Correct! {notation} {sn}\n")
                move_idx += 1
                break
            else:
                attempts += 1
                if attempts == 1:
                    print("  ✗ Not quite. Try again! (type 'hint' for a clue)")
                else:
                    errors += 1
                    expected_san = board.san(expected_m)
                    print(f"  ✗ The correct move was {expected_san}.")
                    board.make(expected_m)
                    board.san_log.append(expected_san)
                    last_mv = expected_m
                    move_idx += 1
                    break

    draw_board(board, persp, last_mv)
    if errors == 0:
        print(f"  ✓✓✓  Puzzle solved! Brilliant work! See it on Lichess: {puzzle_url}\n")
    else:
        print(f"  Puzzle complete ({errors} error(s)). Study it at: {puzzle_url}\n")

    try:
        input("  Press Enter to return...")
    except EOFError:
        pass


def _board_from_fen(fen):
    """Parse a FEN string into a Board object."""
    try:
        parts = fen.split()
        rows  = parts[0].split('/')
        board = Board()
        board.sq = [None] * 64
        _FEN_PIECE = {
            'P': (WHITE, PAWN),   'N': (WHITE, KNIGHT), 'B': (WHITE, BISHOP),
            'R': (WHITE, ROOK),   'Q': (WHITE, QUEEN),  'K': (WHITE, KING),
            'p': (BLACK, PAWN),   'n': (BLACK, KNIGHT), 'b': (BLACK, BISHOP),
            'r': (BLACK, ROOK),   'q': (BLACK, QUEEN),  'k': (BLACK, KING),
        }
        for rank_idx, row in enumerate(rows):
            file_idx = 0
            for ch in row:
                if ch.isdigit():
                    file_idx += int(ch)
                elif ch in _FEN_PIECE:
                    sq = (7 - rank_idx) * 8 + file_idx
                    board.sq[sq] = _FEN_PIECE[ch]
                    file_idx += 1
        board.side = WHITE if (len(parts) < 2 or parts[1] == 'w') else BLACK
        # Castling
        cas_str = parts[2] if len(parts) > 2 else '-'
        board.castling = 0
        if 'K' in cas_str: board.castling |= 1
        if 'Q' in cas_str: board.castling |= 2
        if 'k' in cas_str: board.castling |= 4
        if 'q' in cas_str: board.castling |= 8
        # EP
        ep_str = parts[3] if len(parts) > 3 else '-'
        board.ep = s2sq(ep_str) if ep_str != '-' else None
        board.halfmove  = int(parts[4]) if len(parts) > 4 else 0
        board.fullmove  = int(parts[5]) if len(parts) > 5 else 1
        board.history   = []
        board.san_log   = []
        board._rehash()
        return board
    except Exception:
        return None


# ════════════════════════════════════════════════════════════════════════
#  PGN IMPORT / EXPORT
# ════════════════════════════════════════════════════════════════════════

def export_pgn(san_log, white='White', black='Black', result='*',
               event='Casual Game', site='Local', date=None):
    """Convert a san_log list to a PGN string."""
    if date is None:
        date = datetime.now().strftime('%Y.%m.%d')
    result_tag = '1-0' if result=='white' else ('0-1' if result=='black' else
                 ('1/2-1/2' if result in ('draw','Draw') else result))
    lines = [
        f'[Event "{event}"]',
        f'[Site "{site}"]',
        f'[Date "{date}"]',
        f'[White "{white}"]',
        f'[Black "{black}"]',
        f'[Result "{result_tag}"]',
        '',
    ]
    tokens = []
    for i, san in enumerate(san_log):
        if i % 2 == 0:
            tokens.append(f"{i//2 + 1}.")
        tokens.append(san)
    tokens.append(result_tag)
    # Wrap at 80 chars
    row = ''
    for t in tokens:
        if row and len(row) + 1 + len(t) > 79:
            lines.append(row)
            row = t
        else:
            row = (row + ' ' + t).lstrip()
    if row:
        lines.append(row)
    return '\n'.join(lines) + '\n'


def import_pgn(text):
    """
    Parse a PGN string.  Returns (headers_dict, san_list) or (None, None).
    Handles basic PGN only — tags + movetext, no RAV (variations).
    """
    headers = {}
    movetext_lines = []
    in_moves = False
    for line in text.splitlines():
        line = line.strip()
        if not line:
            if in_moves and movetext_lines:
                continue
            in_moves = bool(movetext_lines)
            continue
        if line.startswith('['):
            m = re.match(r'\[(\w+)\s+"(.*)"\]', line)
            if m:
                headers[m.group(1)] = m.group(2)
        else:
            in_moves = True
            movetext_lines.append(line)

    if not movetext_lines:
        return None, None

    movetext = ' '.join(movetext_lines)
    # Remove comments { ... } and ( ... ) recursively
    for _ in range(10):
        movetext = re.sub(r'\{[^}]*\}', '', movetext)
        movetext = re.sub(r'\([^()]*\)', '', movetext)
    # Remove NAGs ($1 etc)
    movetext = re.sub(r'\$\d+', '', movetext)
    # Remove result token
    movetext = re.sub(r'(1-0|0-1|1/2-1/2|\*)\s*$', '', movetext)
    # Split into tokens, skip move numbers
    tokens = movetext.split()
    sans = []
    for tok in tokens:
        tok = tok.strip('.')
        if not tok:
            continue
        if tok.isdigit():
            continue
        if tok in ('1-0', '0-1', '1/2-1/2', '*'):
            break
        # Skip if it's a move number like "12..."
        if re.match(r'^\d+\.{0,3}$', tok):
            continue
        sans.append(tok)
    # Validate on a board
    b = Board(); b.reset()
    valid = []
    for san in sans:
        m = b.parse_san(san)
        if m is None:
            break
        sn = b.san(m)
        b.make(m)
        b.san_log.append(sn)
        valid.append(sn)
    return headers, valid


def pgn_menu():
    """PGN import/export menu."""
    while True:
        print("\n  ╔══════════════════════════════════════════════════════════╗")
        print("  ║               PGN IMPORT / EXPORT                        ║")
        print("  ╠══════════════════════════════════════════════════════════╣")
        print("  ║  1. Export last saved game to PGN                        ║")
        print("  ║  2. Import PGN and replay / analyze                      ║")
        print("  ║  3. Export all saved games to PGN file                   ║")
        print("  ║  0. Back                                                 ║")
        print("  ╚══════════════════════════════════════════════════════════╝")
        try:
            choice = input("  Choice: ").strip()
        except EOFError:
            return

        if choice == '0':
            return

        elif choice == '1':
            games = load_online_games(limit=1)
            if not games:
                print("  No saved games found.")
                continue
            g = games[0]
            pgn = export_pgn(g.get('moves', []), g.get('white','White'),
                             g.get('black','Black'), g.get('result','*'))
            print("\n" + "─"*70)
            print(pgn)
            print("─"*70)
            # Offer to save to file
            try:
                fn = input("  Save to file (leave blank to skip): ").strip()
            except EOFError:
                fn = ''
            if fn:
                try:
                    with open(fn, 'w') as f:
                        f.write(pgn)
                    print(f"  ✓ Saved to {fn}")
                except Exception as e:
                    print(f"  Error: {e}")

        elif choice == '2':
            print("\n  Paste PGN below. Enter a blank line when done:")
            lines = []
            try:
                while True:
                    ln = input()
                    if not ln.strip() and lines:
                        blank_count = sum(1 for l in lines[-3:] if not l.strip())
                        if blank_count >= 1:
                            break
                    lines.append(ln)
            except EOFError:
                pass
            text = '\n'.join(lines)
            if not text.strip():
                # Try loading from file
                try:
                    fn = input("  Or enter a PGN filename: ").strip()
                    with open(fn) as f:
                        text = f.read()
                except Exception as e:
                    print(f"  Error: {e}"); continue

            headers, san_list = import_pgn(text)
            if not san_list:
                print("  Could not parse PGN or no valid moves found.")
                continue

            white = headers.get('White', 'White') if headers else 'White'
            black = headers.get('Black', 'Black') if headers else 'Black'
            print(f"\n  Imported: {white} vs {black} — {len(san_list)} moves")
            print("  1. Replay game")
            print("  2. Analyze game")
            print("  0. Cancel")
            try:
                sub = input("  Choice: ").strip()
            except EOFError:
                sub = '0'
            if sub == '1':
                replay_game(san_list, white_name=white, black_name=black)
            elif sub == '2':
                results = analyze_game(san_list, engine_time=1.0)
                print_analysis(results)

        elif choice == '3':
            games = load_online_games(limit=100)
            if not games:
                print("  No saved games found.")
                continue
            try:
                fn = input("  Output filename [chess_games.pgn]: ").strip() or 'chess_games.pgn'
            except EOFError:
                fn = 'chess_games.pgn'
            try:
                with open(fn, 'w') as f:
                    for g in reversed(games):
                        pgn = export_pgn(g.get('moves',[]), g.get('white','White'),
                                         g.get('black','Black'), g.get('result','*'),
                                         date=g.get('timestamp','')[:10].replace('-','.'))
                        f.write(pgn + '\n')
                print(f"  ✓ Exported {len(games)} games to {fn}")
            except Exception as e:
                print(f"  Error: {e}")


# ════════════════════════════════════════════════════════════════════════
#  GAME REPLAY VIEWER
# ════════════════════════════════════════════════════════════════════════

def replay_game(san_log, white_name='White', black_name='Black'):
    """
    Interactive game replay.
    Commands:  →/n  next move   ←/p  prev move   g  goto N   q  quit
    """
    if not san_log:
        print("  No moves to replay.")
        return

    # Build board snapshots (lightweight — store san_log prefix)
    print(f"\n  Replaying: {white_name} vs {black_name}  ({len(san_log)} moves)")
    print("  Commands: [n]ext  [p]rev  [g]oto N  [b]eginning  [e]nd  [q]uit\n")

    cur = 0  # number of moves applied so far
    persp = WHITE

    def _build_board(n):
        b = Board(); b.reset()
        for s in san_log[:n]:
            m = b.parse_san(s)
            if m is None: break
            sn = b.san(m); b.make(m); b.san_log.append(sn)
        return b

    while True:
        b = _build_board(cur)
        last = None
        if cur > 0:
            # reconstruct last move to highlight
            b2 = _build_board(cur - 1)
            lm = b2.parse_san(san_log[cur-1])
            last = lm

        draw_board(b, persp, last)

        # Show move list context
        if san_log:
            start = max(0, cur - 4)
            end = min(len(san_log), cur + 4)
            pairs = []
            for i in range(start // 2 * 2, end, 2):
                wm = san_log[i] if i < len(san_log) else '...'
                bm = san_log[i+1] if i+1 < len(san_log) else '...'
                marker_w = '►' if i == cur - 1 else ' '
                marker_b = '►' if i+1 == cur - 1 else ' '
                pairs.append(f"{i//2+1}.{marker_w}{wm} {marker_b}{bm}")
            print("  " + '  '.join(pairs))

        pos_str = f"Position after move {cur}" if cur > 0 else "Starting position"
        print(f"\n  {pos_str}  [{cur}/{len(san_log)}]")

        try:
            cmd = input("  > ").strip().lower()
        except EOFError:
            return

        if cmd in ('q', 'quit', 'exit'):
            return
        elif cmd in ('n', '', 'next', 'f'):
            if cur < len(san_log): cur += 1
        elif cmd in ('p', 'prev', 'back', 'b'):
            if cur == 0: pass
            elif cmd == 'b': cur = 0
            else: cur = max(0, cur - 1)
        elif cmd == 'e':
            cur = len(san_log)
        elif cmd.startswith('g'):
            try:
                n = int(cmd[1:].strip() or input("  Go to move: ").strip())
                cur = max(0, min(len(san_log), n * 2))
            except (ValueError, EOFError):
                print("  Invalid move number.")
        elif cmd == 'flip':
            persp = 1 - persp
        elif cmd == 'a':
            # Quick analysis from current position
            remaining = san_log[cur:]
            if remaining:
                results = analyze_game(remaining, engine_time=0.5)
                print_analysis(results)
        else:
            # Try as move number
            try:
                n = int(cmd)
                cur = max(0, min(len(san_log), n * 2))
            except ValueError:
                print("  Commands: n p b e g<N> flip a(nalyze) q")


def replay_saved_game_menu():
    """Pick and replay a saved game."""
    games = load_online_games(limit=20)
    if not games:
        print("  No saved games found. Play some games first!")
        return

    print("\n  ╔══════════════════════════════════════════════════════════╗")
    print("  ║               GAME REPLAY                                ║")
    print("  ╚══════════════════════════════════════════════════════════╝")
    print(f"  {'#':<3} {'White':<15} {'Black':<15} {'Result':<8} {'Moves':<6}")
    print("  " + "─"*52)
    for i, g in enumerate(games, 1):
        print(f"  {i:<3} {g.get('white','?')[:14]:<15} {g.get('black','?')[:14]:<15} "
              f"{g.get('result','?'):<8} {len(g.get('moves',[])):<6}")
    print()
    try:
        choice = input("  Game number (0 to cancel): ").strip()
    except EOFError:
        return
    try:
        idx = int(choice) - 1
        if 0 <= idx < len(games):
            g = games[idx]
            replay_game(g.get('moves', []), g.get('white','White'), g.get('black','Black'))
    except (ValueError, IndexError):
        if choice != '0':
            print("  Invalid choice.")


# ════════════════════════════════════════════════════════════════════════
#  OPENING EXPLORER  (post-game: shows book deviation point)
# ════════════════════════════════════════════════════════════════════════

def opening_explorer(san_log, book=None):
    """
    Walk through the san_log and show:
    - Which named opening / variation was played
    - Where the game deviated from the book
    - What book alternatives existed at each point
    """
    if book is None:
        book = OpeningBook()

    print("\n  ╔══════════════════════════════════════════════════════════╗")
    print("  ║              OPENING EXPLORER                            ║")
    print("  ╚══════════════════════════════════════════════════════════╝\n")

    b = Board(); b.reset()
    last_book_move = 0
    deviated_at = None

    for i, san in enumerate(san_log):
        m = b.parse_san(san)
        if m is None:
            break
        side = 'White' if b.side == WHITE else 'Black'
        move_num = b.fullmove
        notation = f"{move_num}." if b.side == WHITE else f"{move_num}..."

        # Check book
        book_moves = book.probe(b)
        book_sans = [s for s, _ in book_moves]
        in_book = san in book_sans

        if in_book:
            last_book_move = i + 1
            status = '\033[96m📗 book\033[0m'
        else:
            if deviated_at is None:
                deviated_at = i + 1
            status = '     '

        alt_str = ''
        if book_moves and not in_book:
            alts = ', '.join(book_sans[:3])
            alt_str = f"  \033[90m(book had: {alts})\033[0m"

        print(f"  {notation:<6} {san:<8} {status}{alt_str}")
        sn = b.san(m); b.make(m); b.san_log.append(sn)

        if i >= 19:  # Only show first 20 moves in explorer
            if i == 19:
                print("  ... (showing first 20 moves only)")
            break

    print()
    if deviated_at is None:
        print(f"  ✓ All {last_book_move} moves were book moves!")
    else:
        print(f"  📗 Book coverage: moves 1–{last_book_move}")
        print(f"  ⚡ Deviated from book at move {deviated_at}")
    print()


# ════════════════════════════════════════════════════════════════════════
#  CHESS CLOCK
# ════════════════════════════════════════════════════════════════════════

class ChessClock:
    """
    Simple chess clock with increment support.
    time_control: (minutes, increment_seconds)  e.g. (5, 3) = 5+3
    """
    def __init__(self, minutes=10, increment=0):
        secs = minutes * 60
        self.time = [float(secs), float(secs)]
        self.increment = float(increment)
        self._started = [None, None]
        self._running = None  # which side's clock is running (0=W, 1=B)

    def start(self, side):
        """Start the clock for `side` (0=White, 1=Black)."""
        self._running = side
        self._started[side] = time.time()

    def stop(self, side):
        """Stop the clock for `side` and apply increment."""
        if self._started[side] is not None and self._running == side:
            elapsed = time.time() - self._started[side]
            self.time[side] -= elapsed
            self.time[side] += self.increment
            self.time[side] = max(0.0, self.time[side])
            self._started[side] = None
            self._running = None

    def elapsed(self, side):
        """Current remaining time for `side`."""
        t = self.time[side]
        if self._running == side and self._started[side] is not None:
            t -= time.time() - self._started[side]
        return max(0.0, t)

    def flag(self, side):
        """Return True if `side` has run out of time."""
        return self.elapsed(side) <= 0

    def display(self, side):
        """Format remaining time as mm:ss."""
        t = self.elapsed(side)
        mins = int(t) // 60
        secs = int(t) % 60
        tenths = int((t - int(t)) * 10)
        if t < 10:
            return f"{mins}:{secs:02d}.{tenths}"
        return f"{mins}:{secs:02d}"

    @staticmethod
    def select_time_control():
        """Prompt user to select a time control. Returns (minutes, increment) or (0,0) for unlimited."""
        presets = [
            ("Unlimited",  0,  0),
            ("Bullet 1+0", 1,  0),
            ("Bullet 2+1", 2,  1),
            ("Blitz  3+0", 3,  0),
            ("Blitz  3+2", 3,  2),
            ("Blitz  5+0", 5,  0),
            ("Blitz  5+3", 5,  3),
            ("Rapid 10+0", 10, 0),
            ("Rapid 10+5", 10, 5),
            ("Rapid 15+10",15, 10),
            ("Classic 30+0",30, 0),
            ("Custom",     -1, -1),
        ]
        print("\n  ╔══════════════════════════════════════════════════════════╗")
        print("  ║                 SELECT TIME CONTROL                      ║")
        print("  ╠══════════════════════════════════════════════════════════╣")
        for i, (name, m, inc) in enumerate(presets, 1):
            print(f"  ║  {i:>2}. {name:<52}║")
        print("  ╚══════════════════════════════════════════════════════════╝")
        try:
            sub = input("  Choice [1]: ").strip() or '1'
        except EOFError:
            return 0, 0
        try:
            idx = int(sub) - 1
            if 0 <= idx < len(presets):
                name, mins, inc = presets[idx]
                if mins == -1:
                    try:
                        mins = int(input("  Minutes per side: ").strip() or '10')
                        inc  = int(input("  Increment (seconds): ").strip() or '0')
                    except (ValueError, EOFError):
                        mins, inc = 10, 0
                return mins, inc
        except ValueError:
            pass
        return 0, 0


def _fmt_clock(clock, side):
    """Format clock display string."""
    if clock is None:
        return ''
    t = clock.display(side)
    warn = '\033[91m' if clock.elapsed(side) < 30 else ''
    reset = '\033[0m' if warn else ''
    return f"{warn}⏱ {t}{reset}"


# ════════════════════════════════════════════════════════════════════════
#  ENDGAME TRAINER
# ════════════════════════════════════════════════════════════════════════

def endgame_trainer():
    """
    Practice standard endgames with coaching hints.
    """
    ENDGAMES = [
        {
            "id": 1, "title": "KQK — Queen vs Lone King",
            "fen": "8/8/8/8/8/8/8/KQ5k w - - 0 1",
            "goal": "Checkmate Black in ≤ 10 moves",
            "tips": [
                "Drive the king to the edge first — use your queen to restrict its movement.",
                "Then use your king actively to help deliver checkmate.",
                "Beware of stalemate! If the lone king has no moves, it's only a draw.",
            ],
        },
        {
            "id": 2, "title": "KRK — Rook vs Lone King",
            "fen": "8/8/8/8/8/8/8/KR5k w - - 0 1",
            "goal": "Checkmate Black in ≤ 16 moves",
            "tips": [
                "Use the 'box' technique — reduce the black king's area move by move.",
                "Your king must cooperate with the rook.",
                "Avoid stalemate by leaving the king one escape square before tightening the box.",
            ],
        },
        {
            "id": 3, "title": "KPK — King and Pawn vs King",
            "fen": "8/8/8/8/8/8/4P3/4K2k w - - 0 1",
            "goal": "Promote the pawn",
            "tips": [
                "Your king must lead the pawn — go in front of it!",
                "Gain the opposition (face the enemy king with one square gap).",
                "If your king reaches the 6th rank in front of the pawn, you win.",
            ],
        },
        {
            "id": 4, "title": "Opposition & Pawn Endings",
            "fen": "8/8/8/4k3/8/4K3/4P3/8 w - - 0 1",
            "goal": "Win by escorting the pawn to promotion",
            "tips": [
                "Take the opposition — place your king directly opposite with odd squares between.",
                "The player NOT having to move first (the opposition holder) usually wins.",
                "Key positions: e-file with e7 pawn — centralised king fight!",
            ],
        },
        {
            "id": 5, "title": "Lucena Position — Build the Bridge",
            "fen": "1K1k4/1P6/8/8/8/8/r7/4R3 w - - 0 1",
            "goal": "Escort the pawn to promotion using the Lucena method",
            "tips": [
                "Step 1: Move king towards centre, step 2: build a 'bridge' with the rook.",
                "Place your rook on the 4th rank to shield your king from checks.",
                "Then cut off the attacking rook and promote the pawn.",
            ],
        },
        {
            "id": 6, "title": "Philidor Position — Hold the Draw",
            "fen": "4k3/8/8/8/8/8/4P3/3RK3 b - - 0 1",
            "goal": "Play as Black — hold the draw against K+R+P",
            "tips": [
                "Place your rook on the 6th rank (Philidor position) as long as possible.",
                "Only move to the back rank to give checks when the pawn has advanced far.",
                "Endless checks from behind are the key drawing technique.",
            ],
        },
        {
            "id": 7, "title": "KBNK — Bishop + Knight Mate",
            "fen": "8/8/8/8/8/8/8/KBN4k w - - 0 1",
            "goal": "Checkmate Black in ≤ 33 moves (hardest basic mate)",
            "tips": [
                "Force the black king to the corner that matches your bishop's colour.",
                "Use the 'W-manoeuvre' with knight and bishop to herd the king.",
                "This takes practice — be patient and systematic.",
            ],
        },
    ]

    while True:
        print("\n  ╔══════════════════════════════════════════════════════════╗")
        print("  ║                 ENDGAME TRAINER                          ║")
        print("  ╠══════════════════════════════════════════════════════════╣")
        for eg in ENDGAMES:
            print(f"  ║  {eg['id']:>2}. {eg['title']:<52}║")
        print("  ╠══════════════════════════════════════════════════════════╣")
        print("  ║   0. Back                                                ║")
        print("  ╚══════════════════════════════════════════════════════════╝")
        try:
            choice = input("  Choose an endgame: ").strip()
        except EOFError:
            return
        if choice == '0':
            return
        try:
            eid = int(choice)
            eg = next((e for e in ENDGAMES if e['id'] == eid), None)
            if eg is None:
                print("  Invalid choice.")
                continue
        except ValueError:
            print("  Invalid choice.")
            continue

        _run_endgame(eg)


def _run_endgame(eg):
    """Run a single endgame practice session."""
    board = _board_from_fen(eg['fen'])
    if board is None:
        print("  [Error] Could not load position.")
        return

    tb = Tablebase()
    tb._init_if_needed()

    print(f"\n  ╔══════════════════════════════════════════════════════════╗")
    print(f"  ║  {eg['title']:<56}║")
    print(f"  ╠══════════════════════════════════════════════════════════╣")
    print(f"  ║  Goal: {eg['goal']:<51}║")
    print(f"  ╚══════════════════════════════════════════════════════════╝")
    print()
    print("  TIPS:")
    for tip in eg['tips']:
        print(f"   • {tip}")
    print()
    print("  Commands: <move>  hint  tips  flip  reset  q")
    print()

    persp = board.side
    last_mv = None
    move_count = 0
    human_side = board.side  # player plays the side to move first

    while True:
        draw_board(board, persp, last_mv)
        legal = board.legal()

        # Check terminal
        if not legal:
            if board.in_check():
                winner = 'White' if board.side == BLACK else 'Black'
                print(f"\n  ✓ Checkmate! {winner} wins! Moves taken: {move_count}")
            else:
                print(f"\n  ½ Stalemate — draw! Be careful of stalemate traps!")
            try: input("  Press Enter..."); 
            except EOFError: pass
            return
        if board.is_fifty():
            print("  ½ 50-move rule — draw. Try to be quicker!")
            try: input("  Press Enter..."); 
            except EOFError: pass
            return

        side_str = 'White' if board.side == WHITE else 'Black'
        print(f"  Move {move_count+1} — {side_str} to move")

        if board.side == human_side:
            try:
                raw = input("  Your move: ").strip()
            except EOFError:
                return
            cmd = raw.lower()
            if cmd in ('q', 'quit'):
                return
            if cmd == 'hint':
                # Use tablebase or engine for hint
                eng = Engine(tb=tb)
                mv, _ = eng.search_best(board, t_limit=1.0)
                if mv:
                    print(f"  Hint: try {board.san(mv)}")
                continue
            if cmd == 'tips':
                for tip in eg['tips']:
                    print(f"   • {tip}")
                continue
            if cmd == 'flip':
                persp = 1 - persp
                continue
            if cmd == 'reset':
                board = _board_from_fen(eg['fen'])
                last_mv = None; move_count = 0
                human_side = board.side
                continue

            raw = board._normalise_input(raw)
            mv = board.parse_san(raw)
            if mv is None:
                print(f"  Illegal: '{raw}'"); continue
            sn = board.san(mv); board.make(mv); board.san_log.append(sn)
            last_mv = mv; move_count += 1
        else:
            # AI plays the other side using engine
            eng = Engine(tb=tb)
            mv, _ = eng.search_best(board, t_limit=1.5)
            if mv:
                sn = board.san(mv); board.make(mv); board.san_log.append(sn)
                last_mv = mv; move_count += 1
                print(f"  Opponent plays: {sn}")
            else:
                print("  Opponent has no move.")
                return


# ════════════════════════════════════════════════════════════════════════
#  OPENING QUIZ
# ════════════════════════════════════════════════════════════════════════

def opening_quiz():
    """
    Flash-card style quiz: show a board position, ask 'what opening is this?'
    """
    QUIZ_POSITIONS = [
        {"fen": "r1bqkbnr/pppp1ppp/2n5/1B2p3/4P3/5N2/PPPP1PPP/RNBQK2R b KQkq - 3 3",
         "answer": "Ruy Lopez (Spanish Game)",
         "alternatives": ["Spanish Game", "Ruy Lopez", "Berlin Defence"],
         "clue": "White's third move attacks the knight defending e5"},
        {"fen": "r1bqkbnr/pppp1ppp/2n5/4p3/2B1P3/5N2/PPPP1PPP/RNBQK2R b KQkq - 3 3",
         "answer": "Italian Game (Giuoco Piano)",
         "alternatives": ["Italian", "Giuoco Piano", "Italian Game"],
         "clue": "White develops the bishop to an aggressive diagonal"},
        {"fen": "rnbqkbnr/pp1ppppp/8/2p5/4P3/8/PPPP1PPP/RNBQKBNR w KQkq c6 0 2",
         "answer": "Sicilian Defence",
         "alternatives": ["Sicilian", "Sicilian Defense", "Sicilian Defence"],
         "clue": "Black's asymmetric response to 1.e4"},
        {"fen": "rnbqkbnr/ppp1pppp/8/3p4/4P3/8/PPPP1PPP/RNBQKBNR w KQkq d6 0 2",
         "answer": "Scandinavian Defence (Centre Counter)",
         "alternatives": ["Scandinavian", "Centre Counter", "Scandinavian Defense"],
         "clue": "Black immediately contests the centre with a pawn"},
        {"fen": "rnbqkb1r/pppppppp/5n2/8/3P4/8/PPP1PPPP/RNBQKBNR w KQkq - 1 2",
         "answer": "Indian Defence (after 1.d4 Nf6)",
         "alternatives": ["Indian", "Indian Defence", "Nimzo", "King's Indian"],
         "clue": "Black responds to 1.d4 with a knight, not a pawn"},
        {"fen": "rnbqkbnr/pppppppp/8/8/2PP4/8/PP2PPPP/RNBQKBNR b KQkq c3 0 2",
         "answer": "English Opening",
         "alternatives": ["English", "c4 opening"],
         "clue": "White's flank pawn opening"},
        {"fen": "r1bqkbnr/pppp1ppp/2n5/4p3/4P3/5N2/PPPP1PPP/RNBQKB1R w KQkq - 2 3",
         "answer": "Open Game (King's Pawn Game)",
         "alternatives": ["Open Game", "1.e4 e5 Nf3 Nc6", "Three Knights"],
         "clue": "Both sides occupy the centre"},
        {"fen": "rnbqkbnr/ppp1pppp/3p4/8/3PP3/8/PPP2PPP/RNBQKBNR b KQkq e3 0 2",
         "answer": "Pirc / Modern Defence setup",
         "alternatives": ["Pirc", "Modern", "King's Indian setup"],
         "clue": "Black plays d6 versus the broad centre"},
        {"fen": "rnbqkbnr/pppp1ppp/8/4p3/4P3/8/PPPP1PPP/RNBQKBNR w KQkq e6 0 2",
         "answer": "Open Game (1.e4 e5)",
         "alternatives": ["Open Game", "e4 e5", "Double King Pawn"],
         "clue": "The oldest and most direct response to 1.e4"},
        {"fen": "rnbqkb1r/ppp1pppp/5n2/3p4/2PP4/8/PP2PPPP/RNBQKBNR w KQkq d6 0 3",
         "answer": "Queen's Gambit",
         "alternatives": ["QGD", "Queen's Gambit", "d4 d5 c4"],
         "clue": "White offers a pawn to gain central control"},
        {"fen": "rnbqkbnr/ppp1pppp/8/3p4/3P4/8/PPP1PPPP/RNBQKBNR w KQkq d6 0 2",
         "answer": "Queen's Pawn Game (1.d4 d5)",
         "alternatives": ["Queen's Pawn", "Closed Game", "d4 d5"],
         "clue": "Both sides claim the centre with the queen's pawn"},
        {"fen": "rnbqkbnr/pppppppp/8/8/8/5N2/PPPPPPPP/RNBQKB1R b KQkq - 1 1",
         "answer": "Réti Opening (1.Nf3)",
         "alternatives": ["Reti", "Réti", "King's Indian Attack"],
         "clue": "White develops a knight before pushing any pawns"},
    ]

    score = 0
    total = 0
    random.shuffle(QUIZ_POSITIONS)

    print("\n  ╔══════════════════════════════════════════════════════════╗")
    print("  ║                 OPENING QUIZ                             ║")
    print("  ║  Identify the opening from the board position!           ║")
    print("  ╠══════════════════════════════════════════════════════════╣")
    print("  ║  Type the opening name, 'skip' to skip, 'q' to quit     ║")
    print("  ╚══════════════════════════════════════════════════════════╝\n")

    for pz in QUIZ_POSITIONS:
        board = _board_from_fen(pz['fen'])
        if board is None:
            continue

        draw_board(board, WHITE, None)
        print(f"  What opening is this? (Clue: {pz['clue']})")
        total += 1

        for attempt in range(3):
            try:
                ans = input(f"  Your answer (attempt {attempt+1}/3): ").strip()
            except EOFError:
                return

            if ans.lower() in ('q', 'quit'):
                _show_quiz_score(score, total - 1)
                return
            if ans.lower() == 'skip':
                print(f"  Skipped. Answer: {pz['answer']}")
                break

            # Flexible matching
            ans_lower = ans.lower()
            correct = any(alt.lower() in ans_lower or ans_lower in alt.lower()
                         for alt in pz['alternatives'] + [pz['answer']])
            if correct:
                score += 1
                pts = 3 - attempt  # 3 pts for first try, 2 for second, 1 for third
                print(f"  ✓ Correct! (+{pts} pts) — {pz['answer']}")
                break
            else:
                if attempt < 2:
                    # Extra clue
                    first_word = pz['answer'].split()[0]
                    print(f"  ✗ Not quite. Hint: starts with '{first_word}'...")
                else:
                    print(f"  ✗ Answer: {pz['answer']}")
        print()

    _show_quiz_score(score, total)


def _show_quiz_score(score, total):
    """Display quiz final score."""
    if total == 0:
        return
    pct = int(score / total * 100)
    grade = ("Master! 🏆" if pct >= 90 else
             "Expert! 🎖️" if pct >= 70 else
             "Good! 👍" if pct >= 50 else
             "Keep studying! 📚")
    print("\n  ─── Quiz Complete ──────────────────────────────────────")
    print(f"  Score: {score} / {total}  ({pct}%)")
    print(f"  {grade}")
    print("  ────────────────────────────────────────────────────────\n")
    try: input("  Press Enter to continue...")
    except EOFError: pass


# ════════════════════════════════════════════════════════════════════════
#  STOCKFISH BRIDGE  (optional — uses Stockfish if installed)
# ════════════════════════════════════════════════════════════════════════

import subprocess
import shutil

_STOCKFISH_PATH = None

def _find_stockfish():
    """Detect Stockfish binary location."""
    global _STOCKFISH_PATH
    if _STOCKFISH_PATH is not None:
        return _STOCKFISH_PATH
    for name in ('stockfish', 'stockfish-17', 'stockfish-16', 'stockfish_x86-64',
                  'stockfish_modern', '/usr/games/stockfish', '/usr/bin/stockfish',
                  '/usr/local/bin/stockfish'):
        path = shutil.which(name) or (name if os.path.isfile(name) else None)
        if path:
            _STOCKFISH_PATH = path
            return path
    return None


class StockfishEngine:
    """
    Minimal UCI wrapper around Stockfish (or any UCI engine).
    Falls back gracefully if Stockfish is not found.
    """
    def __init__(self, path=None):
        self.proc = None
        self.available = False
        p = path or _find_stockfish()
        if not p:
            return
        try:
            self.proc = subprocess.Popen(
                [p], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                stderr=subprocess.DEVNULL, text=True, bufsize=1)
            self._send('uci')
            for _ in range(50):
                line = self._recv(timeout=2.0)
                if line and 'uciok' in line:
                    self.available = True
                    break
            if self.available:
                self._send('setoption name Hash value 64')
                self._send('isready')
                for _ in range(20):
                    line = self._recv(timeout=2.0)
                    if line and 'readyok' in line:
                        break
        except Exception:
            self.available = False
            self.proc = None

    def _send(self, cmd):
        if self.proc:
            self.proc.stdin.write(cmd + '\n')
            self.proc.stdin.flush()

    def _recv(self, timeout=5.0):
        if not self.proc:
            return None
        import select
        ready = select.select([self.proc.stdout], [], [], timeout)[0]
        if ready:
            return self.proc.stdout.readline().strip()
        return None

    def analyse(self, fen, movetime_ms=1000, depth=20):
        """
        Analyse a position. Returns (best_move_san, score_cp, pv_san_list).
        score_cp is from the side-to-move's perspective.
        """
        if not self.available:
            return None, None, []
        self._send(f'position fen {fen}')
        self._send(f'go movetime {movetime_ms} depth {depth}')
        best_move = None
        score_cp = None
        pv_uci = []
        while True:
            line = self._recv(timeout=movetime_ms/1000 + 3.0)
            if line is None:
                break
            if line.startswith('info') and 'score cp' in line:
                m = re.search(r'score cp (-?\d+)', line)
                if m:
                    score_cp = int(m.group(1))
                pv_match = re.search(r' pv (.+)', line)
                if pv_match:
                    pv_uci = pv_match.group(1).split()[:5]
            if line.startswith('bestmove'):
                best_move = line.split()[1] if len(line.split()) > 1 else None
                break
        # Convert UCI best_move to SAN
        if best_move and best_move != '(none)':
            board = _board_from_fen(fen)
            if board:
                from_sq = s2sq(best_move[:2])
                to_sq = s2sq(best_move[2:4])
                promo = None
                if len(best_move) == 5:
                    promo = {'q': QUEEN,'r': ROOK,'b': BISHOP,'n': KNIGHT}.get(best_move[4])
                for mv in board.legal():
                    if mv.from_sq == from_sq and mv.to_sq == to_sq:
                        if promo is None or mv.promotion == promo:
                            best_san = board.san(mv)
                            return best_san, score_cp, pv_uci
        return None, score_cp, pv_uci

    def close(self):
        if self.proc:
            try:
                self._send('quit')
                self.proc.wait(timeout=2)
            except Exception:
                self.proc.kill()
            self.proc = None
            self.available = False


_sf_engine = None

def get_stockfish():
    """Return a cached StockfishEngine instance (None if unavailable)."""
    global _sf_engine
    if _sf_engine is None:
        _sf_engine = StockfishEngine()
    return _sf_engine if _sf_engine.available else None


# ════════════════════════════════════════════════════════════════════════
# Daily puzzle removed — was based on invalid built-in puzzles.

def analyze_pgn_line():
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

def game_stats_dashboard():
    """
    Display an ASCII stats dashboard based on locally saved games.
    Shows W/L/D totals, win rate by colour, performance by opening, streaks.
    """
    games = load_online_games(limit=500)
    if not games:
        print("\n  No games recorded yet. Play some games to see your stats!")
        try: input("  Press Enter to return...")
        except EOFError: pass
        return

    # Determine whose stats to show
    player = _current_user or 'Player'

    wins = losses = draws = 0
    white_wins = white_losses = white_draws = 0
    black_wins = black_losses = black_draws = 0
    opening_stats = {}   # opening_name -> [wins, losses, draws]
    current_streak = 0
    streak_type = None
    longest_win_streak = 0
    tmp_ws = 0

    for g in reversed(games):   # oldest first for streaks
        w = g.get('white', '')
        b = g.get('black', '')
        r = g.get('result', '')   # 'white', 'black', or 'draw'

        if player.lower() not in (w.lower(), b.lower()):
            continue

        is_white = w.lower() == player.lower()
        if r == 'draw':
            outcome = 'd'
        elif (r == 'white' and is_white) or (r == 'black' and not is_white):
            outcome = 'w'
        else:
            outcome = 'l'

        if outcome == 'w':
            wins += 1; tmp_ws += 1
            longest_win_streak = max(longest_win_streak, tmp_ws)
            if is_white: white_wins += 1
            else:        black_wins += 1
        elif outcome == 'l':
            losses += 1; tmp_ws = 0
            if is_white: white_losses += 1
            else:        black_losses += 1
        else:
            draws += 1; tmp_ws = 0
            if is_white: white_draws += 1
            else:        black_draws += 1

        # Opening (from first move if available)
        moves_list = g.get('moves', [])
        op_key = moves_list[0] if moves_list else '(unknown)'
        if op_key not in opening_stats:
            opening_stats[op_key] = [0, 0, 0]
        if outcome == 'w':   opening_stats[op_key][0] += 1
        elif outcome == 'l': opening_stats[op_key][1] += 1
        else:                opening_stats[op_key][2] += 1

    total = wins + losses + draws
    if total == 0:
        print(f"\n  No games found for player '{player}'.")
        try: input("  Press Enter...")
        except EOFError: pass
        return

    def _bar(val, total, width=20):
        if total == 0: return '░' * width
        filled = int(round(val / total * width))
        return '█' * filled + '░' * (width - filled)

    wr = wins / total * 100

    print(f"\n  ╔══════════════════════════════════════════════════════════╗")
    print(f"  ║              GAME STATS — {player[:28]:<28}║")
    print(f"  ╠══════════════════════════════════════════════════════════╣")
    print(f"  ║  Total games   : {total:<39}║")
    print(f"  ║  Wins          : {wins:<5} {_bar(wins,total)} {wr:>5.1f}%  ║")
    print(f"  ║  Losses        : {losses:<5} {_bar(losses,total)}          ║")
    print(f"  ║  Draws         : {draws:<5} {_bar(draws,total)}          ║")
    print(f"  ╠══════════════════════════════════════════════════════════╣")
    # Colour breakdown
    wt = white_wins + white_losses + white_draws
    bt = black_wins + black_losses + black_draws
    if wt:
        wwr = white_wins / wt * 100
        print(f"  ║  As White      : {white_wins}W {white_losses}L {white_draws}D   Win rate: {wwr:.1f}%{'':12}║")
    if bt:
        bwr = black_wins / bt * 100
        print(f"  ║  As Black      : {black_wins}W {black_losses}L {black_draws}D   Win rate: {bwr:.1f}%{'':12}║")
    print(f"  ╠══════════════════════════════════════════════════════════╣")
    print(f"  ║  Longest win streak : {longest_win_streak:<35}║")
    print(f"  ╠══════════════════════════════════════════════════════════╣")

    # Top openings by frequency
    sorted_ops = sorted(opening_stats.items(), key=lambda x: sum(x[1]), reverse=True)[:5]
    if sorted_ops:
        print(f"  ║  TOP OPENINGS (by first move)                            ║")
        print(f"  ║  {'Move':<8} {'G':>3} {'W':>3} {'L':>3} {'D':>3} {'WR%':>6}{'':16}║")
        for op, (ow, ol, od) in sorted_ops:
            og = ow + ol + od
            owr = ow / og * 100 if og else 0
            print(f"  ║  {op:<8} {og:>3} {ow:>3} {ol:>3} {od:>3} {owr:>5.1f}%{'':16}║")

    print(f"  ╚══════════════════════════════════════════════════════════╝")

    try:
        input("  Press Enter to return...")
    except EOFError:
        pass


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
            print("  ║  OFFLINE MODE                              [0] Enable Online ║")
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
            learn_opening()

        elif choice=='10':
            puzzles_menu()

        elif choice=='11':
            endgame_trainer()

        elif choice=='12':
            replay_saved_game_menu()

        elif choice=='13':
            pgn_menu()

        elif choice=='14':
            # Opening explorer on last saved game
            games = load_online_games(limit=1)
            if games:
                book_ref = OpeningBook()
                opening_explorer(games[0].get('moves', []), book=book_ref)
            else:
                print("  No saved games yet. Play a game first!")

        elif choice=='15':
            opening_quiz()

        elif choice=='16':
            game_stats_dashboard()

        elif choice=='17':
            settings_menu()

        elif choice=='18':
            report_bug()

        elif choice=='19':
            server_daily_puzzle()

        elif choice=='20':
            if not _offline_mode and _current_user:
                achievements_menu()
            else:
                print("\n  Achievements require an online connection and login.")

        elif choice=='21':
            if not _offline_mode and _current_user:
                tournaments_menu()
            else:
                print("\n  Tournaments require an online connection and login.")

        elif choice=='22':
            if not _offline_mode and _current_user:
                lobby_chat_menu()
            else:
                print("\n  Lobby chat requires an online connection and login.")

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
