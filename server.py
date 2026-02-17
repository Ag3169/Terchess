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
from datetime import datetime

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
            self._save_db({"users": {}, "game_history": []})
    
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

    def send(self, msg_type, data='', success=True):
        """Send a message to the client."""
        payload = json.dumps({
            'type': msg_type,
            'success': success,
            'data': data
        }).encode()
        header = struct.pack('>I', len(payload))
        try:
            self.conn.sendall(header + payload)
            return True
        except:
            return False

    def recv(self, timeout=1.0):
        """Receive a message from the client."""
        self.conn.settimeout(timeout)
        try:
            while True:
                if len(self.pending) >= 4:
                    length = struct.unpack('>I', self.pending[:4])[0]
                    if len(self.pending) >= 4 + length:
                        payload = self.pending[4:4 + length]
                        self.pending = self.pending[4 + length:]
                        return json.loads(payload.decode())
                chunk = self.conn.recv(4096)
                if not chunk:
                    return None
                self.pending += chunk
        except socket.timeout:
            return None
        except:
            return None

    def handle_register(self, data):
        """Handle user registration."""
        username = data.get('username', '').strip()
        password = data.get('password', '')
        email = data.get('email', '').strip()

        success, message = self.db.register_user(username, password, email)
        self.send(RESP_SUCCESS if success else RESP_ERROR, message, success)

    def handle_login(self, data):
        """Handle user login."""
        username = data.get('username', '').strip()
        password = data.get('password', '')
        
        success, message = self.db.authenticate_user(username, password)
        if success:
            self.logged_in_user = username
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
        users = self.db.list_users()
        self.send(RESP_USERS, users, True)

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

    def handle_request(self):
        """Main request handling loop."""
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
            elif msg_type == MSG_LOGOUT:
                # Leave queue if in one
                if self.matchmaking and self.logged_in_user:
                    self.matchmaking.leave_queue(self.logged_in_user)
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
            else:
                self.send(RESP_ERROR, f"Unknown message type: {msg_type}", False)

    def close(self):
        """Close the connection."""
        try:
            # Leave queue if in one
            if self.matchmaking and self.logged_in_user:
                self.matchmaking.leave_queue(self.logged_in_user)
            self.conn.close()
        except:
            pass


# ════════════════════════════════════════════════════════════════════════
#  CHESS SERVER
# ════════════════════════════════════════════════════════════════════════
class ChessServer:
    """Main chess server class."""

    def __init__(self, host='0.0.0.0', port=SERVER_PORT):
        self.host = host
        self.port = port
        self.db_manager = DatabaseManager()
        self.matchmaking = MatchmakingManager()
        self.server_socket = None
        self.running = False
        self.clients = []

    def start(self):
        """Start the server."""
        self.server_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self.server_socket.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)

        try:
            self.server_socket.bind((self.host, self.port))
            self.server_socket.listen(5)
            self.running = True

            # Start matchmaking system
            self.matchmaking.start()

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
                    print(f"  [INFO] New connection from {addr[0]}:{addr[1]}")

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
            handler.handle_request()
        except Exception as e:
            print(f"  [ERROR] Client handler error: {e}")
        finally:
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

    def stop(self):
        """Stop the server."""
        self.running = False
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
