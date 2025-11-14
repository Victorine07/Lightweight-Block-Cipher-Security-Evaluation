theory Simon_{block_size}_{key_size}
  imports
    "HOL-Library.Word"
    "HOL.Bit_Operations"
    "HOL.List"
begin

section ‹Simon: generic definitions and key-schedule›

subsection ‹Configuration parameters›

definition get_num_rounds :: "nat ⇒ nat ⇒ nat" where
  "get_num_rounds block_size key_size =
    (if block_size = 32 ∧ key_size = 64 then 32
     else if block_size = 48 ∧ key_size = 72 then 36
     else if block_size = 48 ∧ key_size = 96 then 36
     else if block_size = 64 ∧ key_size = 96 then 42
     else if block_size = 64 ∧ key_size = 128 then 44
     else if block_size = 96 ∧ key_size = 96 then 52
     else if block_size = 96 ∧ key_size = 144 then 54
     else if block_size = 128 ∧ key_size = 128 then 68
     else if block_size = 128 ∧ key_size = 192 then 69
     else if block_size = 128 ∧ key_size = 256 then 72
     else 0)"

definition get_z_array_index :: "nat ⇒ nat ⇒ nat" where
  "get_z_array_index block_size key_size =
    (if block_size = 32 ∧ key_size = 64 then 0
     else if block_size = 48 ∧ key_size = 72 then 0
     else if block_size = 48 ∧ key_size = 96 then 1
     else if block_size = 64 ∧ key_size = 96 then 2
     else if block_size = 64 ∧ key_size = 128 then 3
     else if block_size = 96 ∧ key_size = 96 then 2
     else if block_size = 96 ∧ key_size = 144 then 3
     else if block_size = 128 ∧ key_size = 128 then 2
     else if block_size = 128 ∧ key_size = 192 then 3
     else if block_size = 128 ∧ key_size = 256 then 4
     else 0)"

subsection ‹Z-sequences (62-bit)›

definition z0 :: int where
  "z0 = 0b01100111000011010100100010111110110011100001101010010001011111"

definition z1 :: int where
  "z1 = 0b01011010000110010011111011100010101101000011001001111101110001"

definition z2 :: int where
  "z2 = 0b11001101101001111110001000010100011001001011000000111011110101"

definition z3 :: int where
  "z3 = 0b11110000101100111001010001001000000111101001100011010111011011"

definition z4 :: int where
  "z4 = 0b11110111001001010011000011101000000100011011010110011110001011"

definition get_z_bit_val :: "nat ⇒ nat ⇒ bool" where
  "get_z_bit_val z_idx i =
     (if z_idx = 0 then bit z0 (i mod 62)
      else if z_idx = 1 then bit z1 (i mod 62)
      else if z_idx = 2 then bit z2 (i mod 62)
      else if z_idx = 3 then bit z3 (i mod 62)
      else if z_idx = 4 then bit z4 (i mod 62)
      else False)"

subsection ‹Core round function›

definition F_function :: "'a::len word ⇒ 'a::len word" where
  "F_function x = xor (and (word_rotl 1 x) (word_rotl 8 x)) (word_rotl 2 x)"

definition simon_round :: "'a::len word ⇒ 'a::len word × 'a::len word ⇒ 'a::len word × 'a::len word" where
  "simon_round k xy = (let (x, y) = xy in (xor (xor k (F_function x)) y, x))"

subsection ‹Round constants and key schedule›

definition rho_const :: "nat ⇒ 'a::len word" where
  "rho_const word_size = word_of_int ((2 ^ word_size) - 1) - (3::'a word)"

function gen_key_schedule_rec :: "nat ⇒ nat ⇒ 'a::len word list ⇒ nat ⇒ 'a word list"
where
  "gen_key_schedule_rec block_size key_size current_keys i =
    (let word_size = block_size div 2;
         m = key_size div word_size;
         t = get_num_rounds block_size key_size;
         z_idx = get_z_array_index block_size key_size
     in
     if i ≥ t then current_keys
     else
       gen_key_schedule_rec block_size key_size
        (current_keys @
         [if m = 2 then
            xor (xor (xor
                (current_keys ! (i - 2))
                (F_function (current_keys ! (i - 1))))
                (word_of_int (if (get_z_bit_val z_idx (i - m)) then 1 else 0)))
                (rho_const word_size)
          else if m = 3 then
            xor (xor
                (current_keys ! (i - 3))
                (F_function (current_keys ! (i - 1))))
                (word_of_int (if (get_z_bit_val z_idx (i - m)) then 1 else 0))
          else if m = 4 then
            xor (xor (xor
                (current_keys ! (i - 4))
                (F_function (current_keys ! (i - 1))))
                (word_of_int (if (get_z_bit_val z_idx (i - m)) then 1 else 0)))
                (rho_const word_size)
          else (0::'a word) ] )
        (i + 1))"
  by pat_completeness auto

termination 
  apply (relation "measure (λ(block_size, key_size, current_keys, i). get_num_rounds block_size key_size - i)")
  apply auto
  done

definition generate_key_schedule :: "nat ⇒ nat ⇒ 'a::len word list ⇒ 'a::len word list" where
  "generate_key_schedule block_size key_size initial_keys_list =
     gen_key_schedule_rec block_size key_size initial_keys_list (length initial_keys_list)"

subsection ‹Encryption and decryption iteration›

fun encrypt_iterate :: "'a::len word × 'a::len word ⇒ 'a::len word list ⇒ 'a::len word × 'a::len word" where
  "encrypt_iterate st [] = st"
| "encrypt_iterate st (k#ks) = encrypt_iterate (simon_round k st) ks"

definition encrypt_block :: "nat ⇒ nat ⇒ 'a::len word × 'a::len word ⇒ 'a::len word list ⇒ 'a::len word × 'a::len word" where
  "encrypt_block block_size key_size xy ks = encrypt_iterate xy ks"

definition decrypt_round_inv :: "'a::len word ⇒ 'a::len word × 'a::len word ⇒ 'a::len word × 'a::len word" where
  "decrypt_round_inv k xy_new = (let (x_new, y_new) = xy_new in (y_new, xor (xor x_new k) (F_function y_new)))"

fun decrypt_iterate :: "'a::len word × 'a::len word ⇒ 'a::len word list ⇒ 'a::len word × 'a::len word" where
  "decrypt_iterate st ks = foldl (λst_new k. decrypt_round_inv k st_new) st (rev ks)"

definition decrypt_block :: "nat ⇒ nat ⇒ 'a::len word × 'a::len word ⇒ 'a::len word list ⇒ 'a::len word × 'a::len word" where
  "decrypt_block block_size key_size xy ks = decrypt_iterate xy ks"

subsection ‹Single-round invertibility lemmas›

lemma simon_round_invertibility_forward:
  fixes k :: "'a::len word" and xy :: "'a::len word × 'a::len word"
  shows "decrypt_round_inv k (simon_round k xy) = xy"
  by (cases xy) (simp add: decrypt_round_inv_def simon_round_def F_function_def ac_simps)

lemma simon_round_invertibility_reverse:
  fixes k :: "'a::len word" and xy :: "'a::len word × 'a::len word"
  shows "simon_round k (decrypt_round_inv k xy) = xy"
  by (cases xy) (simp add: decrypt_round_inv_def simon_round_def F_function_def ac_simps)

section ‹Instantiation: Simon {block_size}/{key_size} (specialization)›

(* All parameters are derived from block_size and key_size only *)
definition block_size :: nat where "block_size = {block_size}"
definition key_size :: nat where "key_size = {key_size}"
definition word_size :: nat where "word_size = {word_size}" (* Computed during generation *)
definition num_rounds :: nat where "num_rounds = get_num_rounds block_size key_size"

type_synonym word = "{word_size} word" (* Concrete word size from template replacement *)
type_synonym key_schedule = "word list"
type_synonym state = "word × word"

definition encrypt :: "state ⇒ key_schedule ⇒ state" where
  "encrypt plaintext ks = encrypt_block block_size key_size plaintext ks"

definition decrypt :: "state ⇒ key_schedule ⇒ state" where
  "decrypt ciphertext ks = decrypt_block block_size key_size ciphertext ks"

definition generate_key_schedule :: "word list ⇒ key_schedule" where
  "generate_key_schedule initial_keys_list = generate_key_schedule block_size key_size initial_keys_list"

subsection ‹Invertibility lemmas specialized to {block_size}/{key_size}›

lemma encrypt_decrypt_inverse:
  fixes xy :: "state"
  fixes ks :: "key_schedule"
  assumes "length ks = num_rounds"
  shows "encrypt (decrypt xy ks) ks = xy"
proof (induction ks arbitrary: xy)
  case Nil
  then show ?case
    by (simp add: encrypt_def decrypt_def encrypt_block_def decrypt_block_def 
                  encrypt_iterate.simps decrypt_iterate.simps)
next
  case (Cons k ks')
  define dec_ks' where "dec_ks' = decrypt xy ks'"
  have full_dec_eq: "decrypt xy (k # ks') = decrypt_round_inv k dec_ks'"
    unfolding dec_ks'_def
    by (simp add: decrypt_def decrypt_block_def decrypt_iterate.simps)
  
  have "encrypt (decrypt xy (k # ks')) (k # ks') =
        encrypt (decrypt_round_inv k dec_ks') (k # ks')"
    by (simp add: full_dec_eq)
  also have "... = encrypt_block block_size key_size (decrypt_round_inv k dec_ks') (k # ks')"
    by (simp add: encrypt_def)
  also have "... = encrypt_iterate (decrypt_round_inv k dec_ks') (k # ks')"
    by (simp add: encrypt_block_def)
  also have "... = encrypt_iterate (simon_round k (decrypt_round_inv k dec_ks')) ks'"
    by (simp add: encrypt_iterate.simps)
  also have "... = encrypt_iterate dec_ks' ks'"
    by (simp add: simon_round_invertibility_reverse)
  also have "... = encrypt dec_ks' ks'"
    by (simp add: encrypt_def encrypt_block_def)
  also have "... = xy"
    using Cons.IH unfolding dec_ks'_def by simp
  finally show ?case by simp
qed

lemma decrypt_encrypt_inverse:
  fixes xy :: "state"
  fixes ks :: "key_schedule"
  assumes "length ks = num_rounds"
  shows "decrypt (encrypt xy ks) ks = xy"
proof (induction ks arbitrary: xy)
  case Nil
  then show ?case
    by (simp add: encrypt_def decrypt_def encrypt_block_def decrypt_block_def
                   encrypt_iterate.simps decrypt_iterate.simps)
next
  case (Cons k ks')
  define round1 where "round1 = simon_round k xy"
  define enc_tail where "enc_tail = encrypt round1 ks'"
  define dec_tail where "dec_tail = decrypt enc_tail ks'"
  
  have encrypt_full: "encrypt xy (k # ks') = enc_tail"
    unfolding enc_tail_def round1_def
    by (simp add: encrypt_def encrypt_block_def encrypt_iterate.simps)
  
  have decrypt_full: "decrypt enc_tail (k # ks') = decrypt_round_inv k dec_tail"
  proof -
    have "decrypt enc_tail (k # ks') =
          decrypt_block block_size key_size enc_tail (k # ks')"
      by (simp add: decrypt_def)
    also have "... = decrypt_iterate enc_tail (k # ks')"
      by (simp add: decrypt_block_def)
    also have "... = foldl (λst_new k. decrypt_round_inv k st_new) enc_tail (rev (k # ks'))"
      by (simp add: decrypt_iterate.simps)
    also have "... = foldl (λst_new k. decrypt_round_inv k st_new) enc_tail (rev ks' @ [k])"
      by (simp add: rev.simps)
    also have "... = foldl (λst_new k. decrypt_round_inv k st_new)
                           (foldl (λst_new k. decrypt_round_inv k st_new) enc_tail (rev ks')) [k]"
      by (simp add: foldl_append)
    also have "... = foldl (λst_new k. decrypt_round_inv k st_new) dec_tail [k]"
      unfolding dec_tail_def
      by (simp add: decrypt_def decrypt_block_def decrypt_iterate.simps)
    also have "... = decrypt_round_inv k dec_tail"
      by simp
    finally show ?thesis .
  qed
  
  have dec_tail_eq: "dec_tail = round1"
    unfolding dec_tail_def enc_tail_def round1_def
    using Cons.IH by simp
  
  show ?case
    unfolding encrypt_full decrypt_full dec_tail_eq round1_def
    by (rule simon_round_invertibility_forward)
qed

end