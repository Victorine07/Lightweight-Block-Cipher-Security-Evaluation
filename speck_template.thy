theory Speck_{block_size}_{key_size}
  imports
    "HOL-Library.Word"
    "HOL.Bit_Operations"
    "HOL.List"
begin

section ‹Speck: generic definitions and key-schedule›

subsection ‹Configuration parameters›

definition get_num_rounds :: "nat ⇒ nat ⇒ nat" where
  "get_num_rounds block_size key_size =
      (if block_size = 32 ∧ key_size = 64 then 22
       else if block_size = 48 ∧ key_size = 72 then 22
       else if block_size = 48 ∧ key_size = 96 then 23
       else if block_size = 64 ∧ key_size = 96 then 26
       else if block_size = 64 ∧ key_size = 128 then 27
       else if block_size = 96 ∧ key_size = 96 then 28
       else if block_size = 96 ∧ key_size = 144 then 29
       else if block_size = 128 ∧ key_size = 128 then 32
       else if block_size = 128 ∧ key_size = 192 then 33
       else if block_size = 128 ∧ key_size = 256 then 34
       else 0)"

definition get_shift_params :: "nat ⇒ nat × nat" where
  "get_shift_params block_size =
      (if block_size = 32 then (7, 2) 
       else (8, 3))"

subsection ‹Core round function›

definition speck_enc_round :: "nat ⇒ nat ⇒ 'a::len word ⇒ 'a::len word ⇒ 'a::len word ⇒ ('a::len word × 'a::len word)" where
  "speck_enc_round alpha_shift beta_shift x y k =
      (let rs_x = word_rotr alpha_shift x;
           add_sxy = rs_x + y;
           new_x = xor add_sxy k;
           ls_y = word_rotl beta_shift y;
           new_y = xor new_x ls_y
       in (new_x, new_y))"

definition speck_dec_round :: "nat ⇒ nat ⇒ 'a::len word ⇒ 'a::len word ⇒ 'a::len word ⇒ ('a::len word × 'a::len word)" where
  "speck_dec_round alpha_shift beta_shift k x y =
      (let xor_xy = xor x y;
           new_y = word_rotr beta_shift xor_xy;
           xor_xk = xor x k;
           msub = xor_xk - new_y;
           new_x = word_rotl alpha_shift msub
       in (new_x, new_y))"

subsection ‹Key schedule generation›

function gen_key_schedule_rec :: "nat ⇒ nat ⇒ nat ⇒ 'a::len word list ⇒ 'a::len word list ⇒ nat ⇒ 'a::len word list"
where
  "gen_key_schedule_rec alpha_shift beta_shift t l_keys k_keys i =
    (if i ≥ t then k_keys
     else
         (let (new_l, new_k) = speck_enc_round alpha_shift beta_shift (l_keys ! i) (k_keys ! i) (word_of_nat i)
          in gen_key_schedule_rec alpha_shift beta_shift t (l_keys @ [new_l]) (k_keys @ [new_k]) (i + 1)))"
  by pat_completeness auto

termination by (relation "measure (λ(_, _, t, _, _, i). t - i)") auto

definition generate_key_schedule :: "nat ⇒ nat ⇒ 'a::len word list ⇒ 'a::len word list" where
  "generate_key_schedule block_size key_size key_words =
      (let (alpha_shift, beta_shift) = get_shift_params block_size;
           word_size = block_size div 2;
           m = key_size div word_size;
           num_rounds = get_num_rounds block_size key_size;
           k0 = [hd key_words];
           l0 = take (m - 1) (tl key_words)
       in gen_key_schedule_rec alpha_shift beta_shift num_rounds l0 k0 0)"

subsection ‹Encryption and decryption iteration›

fun encrypt_iterate :: "nat ⇒ nat ⇒ ('a::len word × 'a::len word) ⇒ 'a::len word list ⇒ ('a::len word × 'a::len word)" where
  "encrypt_iterate _ _ st [] = st"
| "encrypt_iterate alpha_shift beta_shift st (k#ks) =
      (let (x', y') = speck_enc_round alpha_shift beta_shift (fst st) (snd st) k
       in encrypt_iterate alpha_shift beta_shift (x', y') ks)"

(* Thin wrappers: mirror SIMON style - do not take/rev inside here. *)
definition encrypt_block :: "nat ⇒ nat ⇒ 'a::len word ⇒ 'a::len word ⇒ 'a::len word list ⇒ ('a::len word × 'a::len word)" where
  "encrypt_block block_size key_size x y ks =
      encrypt_iterate (fst (get_shift_params block_size)) (snd (get_shift_params block_size)) (x, y) ks"

fun decrypt_iterate :: "nat ⇒ nat ⇒ ('a::len word × 'a::len word) ⇒ 'a::len word list ⇒ ('a::len word × 'a::len word)" where
  "decrypt_iterate _ _ st [] = st"
| "decrypt_iterate alpha_shift beta_shift st (k#ks) =
      (let st' = decrypt_iterate alpha_shift beta_shift st ks
       in speck_dec_round alpha_shift beta_shift k (fst st') (snd st'))"

definition decrypt_block :: "nat ⇒ nat ⇒ 'a::len word ⇒ 'a::len word ⇒ 'a::len word list ⇒ ('a::len word × 'a::len word)" where
  "decrypt_block block_size key_size x y ks =
      decrypt_iterate (fst (get_shift_params block_size)) (snd (get_shift_params block_size)) (x, y) ks"

subsection ‹Single-round invertibility lemmas›

lemma word_rotr_rotl_inverse:
  fixes n :: nat and x :: "'a::len word"
  assumes "n < LENGTH('a)"
  shows "word_rotr n (word_rotl n x) = x"
  by (simp)

lemma word_rotl_rotr_inverse:
  fixes n :: nat and x :: "'a::len word"
  assumes "n < LENGTH('a)"
  shows "word_rotl n (word_rotr n x) = x"
  by (simp )

lemma speck_round_invertibility_forward:
  fixes x y k :: "'a::len word"
  fixes alpha_shift beta_shift :: nat
  assumes "alpha_shift < LENGTH('a)" "beta_shift < LENGTH('a)"
  shows "speck_dec_round alpha_shift beta_shift k (fst (speck_enc_round alpha_shift beta_shift x y k))
                             (snd (speck_enc_round alpha_shift beta_shift x y k)) = (x, y)"
proof -
  define x' where "x' = xor (word_rotr alpha_shift x + y) k"
  define y' where "y' = xor x' (word_rotl beta_shift y)"

  have enc_round: "speck_enc_round alpha_shift beta_shift x y k = (x', y')"
    by (simp add: speck_enc_round_def x'_def y'_def Let_def)

  have dec_round_def: "speck_dec_round alpha_shift beta_shift k x' y' = 
        (let xor_xy = xor x' y';
             new_y = word_rotr beta_shift xor_xy;
             xor_xk = xor x' k;
             msub = xor_xk - new_y;
             new_x = word_rotl alpha_shift msub
         in (new_x, new_y))"
    by (simp add: speck_dec_round_def)

  have xor_xy_simp: "xor x' y' = word_rotl beta_shift y"
  proof -
    from y'_def have "xor x' y' = xor x' (xor x' (word_rotl beta_shift y))"
      by simp
    also have "... = word_rotl beta_shift y"
      by (simp add: Word.word_bw_assocs(3) Word.word_bw_comms(3) Word.word_bw_same(3))
    finally show ?thesis .
  qed

  have new_y_simp: "word_rotr beta_shift (xor x' y') = y"
  proof -
    from xor_xy_simp have "word_rotr beta_shift (xor x' y') = word_rotr beta_shift (word_rotl beta_shift y)"
      by simp
    also have "... = y"
      using assms(2) by (simp add: word_rotr_rotl_inverse)
    finally show ?thesis .
  qed

  have xor_xk_simp: "xor x' k = word_rotr alpha_shift x + y"
  proof -
    from x'_def have "xor x' k = xor (xor (word_rotr alpha_shift x + y) k) k"
      by simp
    also have "... = word_rotr alpha_shift x + y"
      by (simp add: Word.word_bw_assocs(3) Word.word_bw_comms(3) Word.word_bw_same(3))
    finally show ?thesis .
  qed

  have msub_simp: "xor x' k - word_rotr beta_shift (xor x' y') = word_rotr alpha_shift x"
  proof -
    from xor_xk_simp new_y_simp show ?thesis
      by (simp add: diff_add_eq)
  qed

  have new_x_simp: "word_rotl alpha_shift (xor x' k - word_rotr beta_shift (xor x' y')) = x"
  proof -
    from msub_simp have "word_rotl alpha_shift (xor x' k - word_rotr beta_shift (xor x' y')) = 
                             word_rotl alpha_shift (word_rotr alpha_shift x)"
      by simp
    also have "... = x"
      using assms(1) by (simp add: word_rotl_rotr_inverse)
    finally show ?thesis .
  qed

  have "speck_dec_round alpha_shift beta_shift k x' y' = 
         (word_rotl alpha_shift (xor x' k - word_rotr beta_shift (xor x' y')),
          word_rotr beta_shift (xor x' y'))"
    by (simp add: speck_dec_round_def Let_def)
  
  then show ?thesis
    using enc_round new_x_simp new_y_simp by simp
qed

lemma speck_round_invertibility_reverse:
  fixes x y k :: "'a::len word"
  fixes alpha_shift beta_shift :: nat
  assumes "alpha_shift < LENGTH('a)" "beta_shift < LENGTH('a)"
  shows "speck_enc_round alpha_shift beta_shift (fst (speck_dec_round alpha_shift beta_shift k x y))
                             (snd (speck_dec_round alpha_shift beta_shift k x y)) k = (x, y)"
proof -
  define new_y where "new_y = word_rotr beta_shift (xor x y)"
  define new_x where "new_x = word_rotl alpha_shift (xor x k - new_y)"

  have dec_round: "speck_dec_round alpha_shift beta_shift k x y = (new_x, new_y)"
    by (simp add: speck_dec_round_def new_x_def new_y_def Let_def)

  have enc_round_def: "speck_enc_round alpha_shift beta_shift new_x new_y k = 
        (let rs_x = word_rotr alpha_shift new_x;
             add_sxy = rs_x + new_y;
             x' = xor add_sxy k;
             ls_y = word_rotl beta_shift new_y;
             y' = xor x' ls_y
         in (x', y'))"
    by (simp add: speck_enc_round_def)

  have rs_x_simp: "word_rotr alpha_shift new_x = xor x k - new_y"
  proof -
    from new_x_def have "word_rotr alpha_shift new_x = word_rotr alpha_shift (word_rotl alpha_shift (xor x k - new_y))"
      by simp
    also have "... = xor x k - new_y"
      using assms(1) by (simp add: word_rotr_rotl_inverse)
    finally show ?thesis .
  qed

  have add_sxy_simp: "word_rotr alpha_shift new_x + new_y = xor x k"
  proof -
    from rs_x_simp have "word_rotr alpha_shift new_x + new_y = (xor x k - new_y) + new_y"
      by simp
    also have "... = xor x k"
      by simp
    finally show ?thesis .
  qed

  have x'_simp: "xor (word_rotr alpha_shift new_x + new_y) k = x"
  proof -
    from add_sxy_simp have "xor (word_rotr alpha_shift new_x + new_y) k = xor (xor x k) k"
      by simp
    also have "... = x"
      by (simp add: Word.word_bw_assocs(3) Word.word_bw_comms(3) Word.word_bw_same(3))
    finally show ?thesis .
  qed

  have ls_y_simp: "word_rotl beta_shift new_y = word_rotl beta_shift (word_rotr beta_shift (xor x y))"
    by (simp add: new_y_def)

  have ls_y_simp2: "word_rotl beta_shift new_y = xor x y"
  proof -
    from ls_y_simp have "word_rotl beta_shift new_y = word_rotl beta_shift (word_rotr beta_shift (xor x y))"
      by simp
    also have "... = xor x y"
      using assms(2) by (simp add: word_rotl_rotr_inverse)
    finally show ?thesis .
  qed

  have y'_simp: "xor (xor (word_rotr alpha_shift new_x + new_y) k) (word_rotl beta_shift new_y) = y"
  proof -
    from x'_simp ls_y_simp2 have "xor (xor (word_rotr alpha_shift new_x + new_y) k) (word_rotl beta_shift new_y) = 
                                 xor x (xor x y)"
      by simp
    also have "... = y"
      by (simp add: Word.word_bw_assocs(3) Word.word_bw_comms(3) Word.word_bw_same(3))
    finally show ?thesis .
  qed

  have "speck_enc_round alpha_shift beta_shift new_x new_y k = 
         (xor (word_rotr alpha_shift new_x + new_y) k, 
          xor (xor (word_rotr alpha_shift new_x + new_y) k) (word_rotl beta_shift new_y))"
    by (simp add: speck_enc_round_def Let_def)
  
  then show ?thesis
    using dec_round x'_simp y'_simp by simp
qed

subsection ‹Helper: iterate-level inverse (critical)›

lemma decrypt_iterate_encrypt_iterate_inverse:
  fixes alpha beta :: nat
  fixes x y :: "'a::len word"
  fixes ks :: "'a::len word list"
  assumes "alpha < LENGTH('a)" "beta < LENGTH('a)"
  shows "decrypt_iterate alpha beta (encrypt_iterate alpha beta (x, y) ks) ks = (x, y)"
proof (induction ks arbitrary: x y)
  case Nil
  then show ?case
    by (simp add: encrypt_iterate.simps decrypt_iterate.simps)
next
  case (Cons k ks')
  define round1 where "round1 = speck_enc_round alpha beta x y k"
  define enc_tail where "enc_tail = encrypt_iterate alpha beta round1 ks'"
  define dec_tail where "dec_tail = decrypt_iterate alpha beta enc_tail ks'"

  (* 1) instantiate the IH for the concrete round1 state *)
  have IH_inst:
    "decrypt_iterate alpha beta (encrypt_iterate alpha beta round1 ks') ks' = round1"
    using Cons.IH[of "fst round1" "snd round1"]
    by (simp add: enc_tail_def round1_def)

  (* 2) use IH_inst to rewrite the 'let' expression into the concrete round1 *)
  have step_subst:
    "(let st' = decrypt_iterate alpha beta (encrypt_iterate alpha beta (speck_enc_round alpha beta x y k) ks') ks'
      in speck_dec_round alpha beta k (fst st') (snd st')) =
      speck_dec_round alpha beta k (fst round1) (snd round1)"
  proof -
    from IH_inst have "decrypt_iterate alpha beta (encrypt_iterate alpha beta (speck_enc_round alpha beta x y k) ks') ks' = round1"
      by (simp add: round1_def)
    thus ?thesis
      by simp
  qed

  (* 3) apply the single-round invertibility lemma to the concrete RHS *)
  have RHS_eq: "speck_dec_round alpha beta k (fst round1) (snd round1) = (x, y)"
    by (simp add: round1_def speck_round_invertibility_forward[OF ‹alpha < LENGTH('a)› ‹beta < LENGTH('a)›])

  (* 4) combine the substitution equality and RHS_eq to finish *)
  from step_subst RHS_eq show ?case
    by simp
qed

(* ---SHOWS  Encrypt followed by decrypt gives original --- *)
lemma encrypt_iterate_decrypt_iterate_inverse:
  fixes alpha beta :: nat
  fixes x y :: "'a::len word"
  fixes ks :: "'a::len word list"
  assumes "alpha < LENGTH('a)" "beta < LENGTH('a)"
  shows "encrypt_iterate alpha beta (decrypt_iterate alpha beta (x, y) ks) ks = (x, y)"
proof (induction ks arbitrary: x y)
  case Nil
  then show ?case
    by simp
next
  case (Cons k ks')
  let ?st' = "decrypt_iterate alpha beta (x, y) ks'"

  (* expand one step of decrypt_iterate/encrypt_iterate for the (k # ks') case *)
  have step:
    "encrypt_iterate alpha beta (decrypt_iterate alpha beta (x, y) (k # ks')) (k # ks') =
      (let (x', y') = speck_enc_round alpha beta
                             (fst (speck_dec_round alpha beta k (fst ?st') (snd ?st')))
                             (snd (speck_dec_round alpha beta k (fst ?st') (snd ?st')))
                             k
      in encrypt_iterate alpha beta (x', y') ks')"
      by (simp add: decrypt_iterate.simps encrypt_iterate.simps Let_def)

  also have "... = encrypt_iterate alpha beta ?st' ks'"
    using speck_round_invertibility_reverse[OF ‹alpha < LENGTH('a)› ‹beta < LENGTH('a)›]
    by simp

  also have "... = (x, y)"
    using Cons.IH by simp

  finally show ?case .
qed

section ‹Instantiation: Speck {block_size}/{key_size} (specialization)›

(* All parameters are derived from block_size and key_size only *)
definition block_size :: nat where "block_size = {block_size}"
definition key_size :: nat where "key_size = {key_size}"
definition word_size :: nat where "word_size = {word_size}" (* Computed during generation *)
definition num_rounds :: nat where "num_rounds = get_num_rounds block_size key_size"

(* Shift parameters computed from block_size *)
definition alpha :: nat where "alpha = fst (get_shift_params block_size)"
definition beta :: nat where "beta = snd (get_shift_params block_size)"

type_synonym word = "{word_size} word" (* Concrete word size from template replacement *)
type_synonym key_schedule = "word list"
type_synonym state = "word × word"

(* Encryption / Decryption definitions *)
definition encrypt :: "word ⇒ word ⇒ key_schedule ⇒ state" where
  "encrypt x y ks = encrypt_block block_size key_size x y ks"

definition decrypt :: "word ⇒ word ⇒ key_schedule ⇒ state" where
  "decrypt x y ks = decrypt_block block_size key_size x y ks"

definition generate_key_schedule :: "word list ⇒ key_schedule" where
  "generate_key_schedule ks = generate_key_schedule block_size key_size ks"

(* Prove shift parameters are valid for the computed word_size *)
lemma shifts_valid: 
  "alpha < {word_size} ∧ beta < {word_size}"
  unfolding alpha_def beta_def word_size_def
            block_size_def get_shift_params_def
  by auto

lemma encrypt_decrypt_inverse:
  fixes x y :: "word" and ks :: "key_schedule"
  shows "decrypt (fst (encrypt x y ks)) (snd (encrypt x y ks)) ks = (x, y)"
proof -
  (* Unfold the thin wrappers to expose the iterate form with computed shifts *)
  have E: "encrypt x y ks = encrypt_iterate alpha beta (x, y) ks"
    unfolding encrypt_def encrypt_block_def get_shift_params_def 
              block_size_def alpha_def beta_def by simp
  have D: "decrypt a b ks = decrypt_iterate alpha beta (a, b) ks" for a b
    unfolding decrypt_def decrypt_block_def get_shift_params_def 
              block_size_def alpha_def beta_def by simp
  (* Reuse the generic inverse: decrypt after encrypt = id *)
  have INV: "decrypt_iterate alpha beta (encrypt_iterate alpha beta (x, y) ks) ks = (x, y)"
    using decrypt_iterate_encrypt_iterate_inverse[of alpha beta x y ks]
          shifts_valid
    by simp
  show ?thesis unfolding E D using INV by simp
qed

lemma decrypt_encrypt_inverse:
  fixes x y :: "word" and ks :: "key_schedule"
  shows "encrypt (fst (decrypt x y ks)) (snd (decrypt x y ks)) ks = (x, y)"
proof -
  (* Unfold the thin wrappers to expose the iterate form with computed shifts *)
  have E: "encrypt a b ks = encrypt_iterate alpha beta (a, b) ks" for a b
    unfolding encrypt_def encrypt_block_def get_shift_params_def 
              block_size_def alpha_def beta_def by simp
  have D: "decrypt x y ks = decrypt_iterate alpha beta (x, y) ks"
    unfolding decrypt_def decrypt_block_def get_shift_params_def 
              block_size_def alpha_def beta_def by simp
  (* Reuse the generic inverse: encrypt after decrypt = id *)
  have INV: "encrypt_iterate alpha beta (decrypt_iterate alpha beta (x, y) ks) ks = (x, y)"
    using encrypt_iterate_decrypt_iterate_inverse[of alpha beta x y ks]
          shifts_valid
    by simp
  show ?thesis unfolding E D using INV by simp
qed

end