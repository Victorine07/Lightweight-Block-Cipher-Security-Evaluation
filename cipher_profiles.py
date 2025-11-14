# cipher_profiles.py

"""
cipher_profiles.py
Cipher Profile definitions and Security Scoring logic.
This version supports Simon (Feistel), Speck (ARX), and PRESENT (SPN) ciphers,
and integrates realistic security scoring and labeling.
"""

import math
from dataclasses import dataclass
from typing import Dict, Any, Tuple

# ============================================================
# ATTACK DATABASE — known attack complexity for cipher variants
# ============================================================

ATTACK_DB ={
    "Simon": {
        (32, 64):   {'total_rounds': 32, 'rounds_broken': 24, 'attack_type': 'integral', 'complexity': 2**63},
        (48, 72):   {'total_rounds': 36, 'rounds_broken': 24, 'attack_type': 'linear_hull', 'complexity': 2**56},
        (48, 96):   {'total_rounds': 36, 'rounds_broken': 25, 'attack_type': 'linear_hull', 'complexity': 2**80},
        (64, 96):   {'total_rounds': 42, 'rounds_broken': 30, 'attack_type': 'linear_hull', 'complexity': 2**88},
        (64, 128):  {'total_rounds': 44, 'rounds_broken': 31, 'attack_type': 'linear_hull', 'complexity': 2**122},
        (96, 96):   {'total_rounds': 52, 'rounds_broken': 37, 'attack_type': 'linear_hull', 'complexity': 2**88},
        (96, 144):  {'total_rounds': 54, 'rounds_broken': 38, 'attack_type': 'linear_hull', 'complexity': 2**136},
        (128, 128): {'total_rounds': 68, 'rounds_broken': 49, 'attack_type': 'linear_hull', 'complexity': 2**120},
        (128, 192): {'total_rounds': 69, 'rounds_broken': 51, 'attack_type': 'linear_hull', 'complexity': 2**184},
        (128, 256): {'total_rounds': 72, 'rounds_broken': 53, 'attack_type': 'linear_hull', 'complexity': 2**248},
    },
    "Speck": {
        (32, 64):   {'total_rounds': 22, 'rounds_broken': 15, 'attack_type': 'differential', 'complexity': 2**63.39},
        (48, 72):   {'total_rounds': 22, 'rounds_broken': 16, 'attack_type': 'differential', 'complexity': 2**71.8},
        (48, 96):   {'total_rounds': 23, 'rounds_broken': 17, 'attack_type': 'differential', 'complexity': 2**95.8},
        (64, 96):   {'total_rounds': 26, 'rounds_broken': 19, 'attack_type': 'differential', 'complexity': 2**93.56},
        (64, 128):  {'total_rounds': 27, 'rounds_broken': 20, 'attack_type': 'differential', 'complexity': 2**125.56},
        (96, 96):   {'total_rounds': 28, 'rounds_broken': 20, 'attack_type': 'differential', 'complexity': 2**95.94},
        (96, 144):  {'total_rounds': 29, 'rounds_broken': 21, 'attack_type': 'differential', 'complexity': 2**143.94},
        (128, 128): {'total_rounds': 32, 'rounds_broken': 23, 'attack_type': 'differential', 'complexity': 2**125.35},
        (128, 192): {'total_rounds': 33, 'rounds_broken': 24, 'attack_type': 'differential', 'complexity': 2**189.35},
        (128, 256): {'total_rounds': 34, 'rounds_broken': 25, 'attack_type': 'differential', 'complexity': 2**253.35},
    },
    "PRESENT": {
        (64, 40):   {'total_rounds': 31, 'rounds_broken': 26, 'attack_type': 'cryptanalytic', 'complexity': 2**3},
        (64, 80):   {'total_rounds': 31, 'rounds_broken': 26, 'attack_type': 'linear', 'complexity': 2**72},
        (64, 128):  {'total_rounds': 31, 'rounds_broken': 26, 'attack_type': 'differential', 'complexity': 2**124},
    },
    "HIGHT": {
        (64, 128):  {'total_rounds': 32, 'rounds_broken': 26, 'attack_type': 'biclique', 'complexity': 2**118}
    }
}


# ============================================================
# SECURITY SCORING SYSTEM (REALISTIC MODEL)
# ============================================================

@dataclass
class SecurityParams:
    """Dynamic security parameters that adjust based on cipher family."""
    
    # STEP 1: Define attributes at the class level.
    # The dataclass will automatically create an __init__ that accepts `cipher_name`.
    cipher_name: str = None
    #_max_params: Dict[str, int] = field(init=False, repr=False)  # Don't include in init
    

    # STEP 2: Move initialization logic to __post_init__.
    # This special method runs right after the dataclass's own __init__ is finished.
    def __post_init__(self):
        """This method is called after the dataclass-generated __init__."""
        self._max_params = self._calculate_max_params()
    
    
    def _calculate_max_params(self) -> Dict[str, int]:
        """Calculate maximum security parameters for the given cipher family."""
        if not self.cipher_name:
            # Default fallback values
            return {
                "max_rounds": 72,
                "max_key_size": 256, 
                "max_block_size": 128
            }
        
        # Cipher-specific maximums based on known variants
        cipher_maxima = {
            "Simon": {
                "max_rounds": 72,      # Simon128_256 has 72 rounds
                "max_key_size": 256,   # Simon128_256 has 256-bit key
                "max_block_size": 128  # Maximum block size for Simon
            },
            "Speck": {
                "max_rounds": 34,      # Speck128_256 has 34 rounds
                "max_key_size": 256,   # Speck128_256 has 256-bit key
                "max_block_size": 128  # Maximum block size for Speck
            },
            "PRESENT": {
                "max_rounds": 31,      # PRESENT has 31 rounds
                "max_key_size": 128,   # PRESENT-128 has 128-bit key
                "max_block_size": 64   # PRESENT has 64-bit block size
            },
            "HIGHT": {
                "max_rounds": 32,      # PRESENT has 31 rounds
                "max_key_size": 128,   # PRESENT-128 has 128-bit key
                "max_block_size": 64   # PRESENT has 64-bit block size
            }
        }
        
        return cipher_maxima.get(self.cipher_name, {
            "max_rounds": 72,
            "max_key_size": 256,
            "max_block_size": 128
        })
        
    @property
    def max_rounds(self) -> int:
        return self._max_params["max_rounds"]
    
    @property
    def max_key_size(self) -> int:
        return self._max_params["max_key_size"]
    
    @property
    def max_block_size(self) -> int:
        return self._max_params["max_block_size"]
    
    def get_params(self) -> Dict[str, int]:
        """Return all parameters as a dictionary."""
        return self._max_params.copy()
    
    def __str__(self) -> str:
        return (f"(max_rounds={self.max_rounds}, "
                f"max_key_size={self.max_key_size}, "
                f"max_block_size={self.max_block_size})")
        
DEFAULT_PARAMS = SecurityParams()


def get_attack_severity(attack_type: str) -> float:
    """
    Return severity factor for different attack types.
    lower values = more concerning attacks.
    """
    severity_map = {
        'brute_force': 1.0,        # Expected baseline
        'linear': 0.9,             # Moderate concern
        'linear_hull': 0.9,        # Moderate concern
        'differential': 0.8,       # Moderate concern  
        'integral': 0.7,           # Moderate concern
        'zero_correlation': 0.6,   # Less common but serious
        'impossible_differential': 0.6,  # Advanced but serious
        'biclique': 0.2,           # Advanced attack
        'related_key': 0.9,        # Very concerning
        'meet_in_middle': 0.8,     # Concerning
        'algebraic': 0.4,          # Theoretical, less practical
        'cryptanalytic': 0.7,      # General cryptanalysis
        None: 1.0                  # No known attacks = best case
    }
    return severity_map.get(attack_type, 0.7)



def compute_security_score(params: SecurityParams, block_size: int, key_size: int,
                          rounds: int, attacks: Dict[str, int], 
                          rounds_broken: int = None, attack_type: str = None) -> float:
    """
    Advanced security scoring that incorporates security margins and attack context.
    """
    # 1. Calculate security margin if rounds_broken is provided
    if rounds_broken is not None and rounds > 0:
        security_margin = (rounds - rounds_broken) / rounds  # Percentage of unbroken rounds
        margin_penalty = 1.0 - security_margin  # Penalty based on how close attack got to full rounds
    else:
        # Conservative assumption: if we don't know rounds broken, assume moderate margin
        security_margin = 0.5
        margin_penalty = 0.5

    # 2. Design strength with security margin consideration
    if rounds is None or rounds == 0:
        weights = {'key_size': 0.6, 'block_size': 0.4}
        design_strength = (
            weights['key_size'] * (key_size / params.max_key_size) +
            weights['block_size'] * (block_size / params.max_block_size)
        )
    else:
        # Incorporate security margin into rounds component
        rounds_strength = (rounds / params.max_rounds) * (1.0 - margin_penalty * 0.5)
        
        weights = {'rounds': 0.3, 'key_size': 0.4, 'block_size': 0.3}
        design_strength = (
            weights['rounds'] * rounds_strength +
            weights['key_size'] * (key_size / params.max_key_size) +
            weights['block_size'] * (block_size / params.max_block_size)
        )

    # 3. Attack-based security with margin penalty
    if attacks:
        security_bits = math.log2(min(attacks.values()))
        # Apply margin penalty to security bits
        adjusted_security_bits = security_bits * (1.0 - margin_penalty * 0.3)
    else:
        # No known attacks = maximum theoretical security
        adjusted_security_bits = min(block_size, key_size)

    # 4. Attack severity factor
    attack_severity = get_attack_severity(attack_type)
    
    # 5. Final security score
    security_score = (adjusted_security_bits / 128) 
    
    # Combined score with attack severity consideration
    final_score = (0.7 * security_score + 0.2 * design_strength + 0.1 * attack_severity) * 10.0

    return round(min(10.0, final_score), 2)

def security_label_from_score(score: float) -> str:
    if score < 5.0:
        return "low"
    elif score < 7:
        return "medium"
    return "high"
    


# ============================================================
# CIPHER PROFILES
# ============================================================

CIPHER_PROFILES = {
    "Simon": {
        "family": "Feistel",
        "variants": {
            "Simon32_64":  {"block_size": 32, "key_size": 64, "rounds": 32},
            "Simon48_72":  {"block_size": 48, "key_size": 72, "rounds": 36},
            "Simon48_96":  {"block_size": 48, "key_size": 96, "rounds": 36},
            "Simon64_96":  {"block_size": 64, "key_size": 96, "rounds": 42},
            "Simon64_128": {"block_size": 64, "key_size": 128, "rounds": 44},
            "Simon96_96":  {"block_size": 96, "key_size": 96, "rounds": 52},
            "Simon96_144": {"block_size": 96, "key_size": 144, "rounds": 54},
            "Simon128_128": {"block_size": 128, "key_size": 128, "rounds": 68},
            "Simon128_192": {"block_size": 128, "key_size": 192, "rounds": 69},
            "Simon128_256": {"block_size": 128, "key_size": 256, "rounds": 72},
        }
    },
    "Speck": {
        "family": "ARX",
        "variants": {
            "Speck32_64":  {"block_size": 32, "key_size": 64, "rounds": 22},
            "Speck48_72":  {"block_size": 48, "key_size": 72, "rounds": 22},
            "Speck48_96":  {"block_size": 48, "key_size": 96, "rounds": 23},
            "Speck64_96":  {"block_size": 64, "key_size": 96, "rounds": 26},
            "Speck64_128": {"block_size": 64, "key_size": 128, "rounds": 27},
            "Speck96_96":  {"block_size": 96, "key_size": 96, "rounds": 28},
            "Speck96_144": {"block_size": 96, "key_size": 144, "rounds": 29},
            "Speck128_128": {"block_size": 128, "key_size": 128, "rounds": 32},
            "Speck128_192": {"block_size": 128, "key_size": 192, "rounds": 33},
            "Speck128_256": {"block_size": 128, "key_size": 256, "rounds": 34},
        }
    },
    "PRESENT": {
        "family": "SPN",
        "variants": {
            "PRESENT64_40":  {"block_size": 64, "key_size": 40, "rounds": 8},
            "PRESENT64_80":  {"block_size": 64, "key_size": 80, "rounds": 31},
            "PRESENT64_128": {"block_size": 64, "key_size": 128, "rounds": 31},
        }
    },
    "HIGHT": {
        "family": "HIGHT_ARX", # HIGHT is a Generalized Feistel Network, but often grouped with ARX.
        "variants": {
            "HIGHT64_128": {"block_size": 64, "key_size": 128, "rounds": 32}
        }
    }
}


# ============================================================
# HELPER — get security info for a given cipher variant
# ============================================================

def get_cipher_security_info(cipher_name: str, variant_name: str) -> Dict[str, Any]:
    """Return cipher configuration enriched with security score and label."""

    
    cipher_entry = CIPHER_PROFILES.get(cipher_name)
    if not cipher_entry:
        raise ValueError(f"Unknown cipher: {cipher_name}")

    variant = cipher_entry["variants"].get(variant_name)
    if not variant:
        raise ValueError(f"Unknown variant: {variant_name}")

    block_size = variant["block_size"]
    key_size = variant["key_size"]
    profile_rounds = variant["rounds"]

    # Get enhanced attack data
    attack_info = ATTACK_DB.get(cipher_name, {}).get((block_size, key_size), {})
    
    if attack_info:
        # Use attack data if available
        rounds = attack_info.get('total_rounds', profile_rounds)
        rounds_broken = attack_info.get('rounds_broken')
        attack_type = attack_info.get('attack_type')
        complexity = attack_info.get('complexity')
        attacks = {attack_type: complexity} if attack_type and complexity else {}
    else:
        # Fall back to profile data
        rounds = profile_rounds
        rounds_broken = None
        attack_type = None
        attacks = {}
    
    params = SecurityParams(cipher_name)
    
    # Use enhanced security scoring
    score = compute_security_score(
        params, block_size, key_size, rounds,
        attacks, rounds_broken, attack_type
    )
    label = security_label_from_score(score)

    return {
        "cipher_name": cipher_name,
        "variant": variant_name,
        "family": cipher_entry["family"],
        "block_size": block_size,
        "key_size": key_size,
        "rounds": rounds,
        "rounds_broken": rounds_broken,
        "security_margin": (rounds - rounds_broken) / rounds if rounds_broken else None,
        "attack_type": attack_type,
        "security_score": score,
        "security_label": label
    }, params



    