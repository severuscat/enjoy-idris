%default total

data DividesNat : (a : Nat) -> (b : Nat) -> Type where
    Div : (k ** (k * x = y)) -> DividesNat y x

data Prime : (p : Nat) -> Type where
    ConsPrime : LTE 2 p ->
        ((d : Nat) -> DividesNat p d -> Either (d = 1) (d = p)) ->
        Prime p

data Even : (a : Nat) -> Type where
    Even_ : a `DividesNat` 2 -> Even a

data Odd : (a : Nat) -> Type where
    Odd_ : {aa : Nat} -> Even aa -> Odd (S aa)

data NEq : (a : Nat) -> (b : Nat) -> Type where
    NEq_ : (a = b -> Void) -> NEq a b


out : S a = S b -> a = b
out Refl = Refl

disjoint : {n : Nat} -> Z = S n -> Void
disjoint {n} p = replace {P = disjointTy} p ()
where
    disjointTy : Nat -> Type
    disjointTy Z = ()
    disjointTy (S k) = Void

evenNotPrime : {a : Nat} -> Even a -> a `GT` 2 -> (Prime a -> Void)
evenNotPrime {a = Z} _ LTEZero _ impossible
evenNotPrime {a = (S Z)} _ (LTESucc LTEZero) _ impossible
evenNotPrime {a = (S (S Z))} _ (LTESucc (LTESucc LTEZero)) _ impossible
evenNotPrime {a = (S (S (S k)))} (Even_ div_2) gt_a (ConsPrime _ f) =
    case f 2 div_2 of
        Left p => lemma_1 p
        Right p => lemma_2 p

    where
        lemma_1 : S (S Z) = S Z -> Void
        lemma_1 prf = disjoint (out (sym prf))

        lemma_2 : {k: Nat} -> S (S Z) = (S (S (S k))) -> Void
        lemma_2 prf = disjoint (out (out prf))

--=================================================================================================================================================================
--f : (d : Nat) -> DividesNat p d -> Either (d = 1) (d = p)
re_out : a = b -> S a = S b
re_out Refl = Refl

-- (2 * a' + 1) + (2 * b' + 1) = 2 * (a' + b') + 2 = 2 * (a' + b' + 1) = a + b
-- k_a is like k_a * 2 = a'
sumOddIsEven : {a, b : Nat} -> Odd a -> Odd b -> Even (a + b)
sumOddIsEven {a = S a_} {b = S b_}
  (Odd_ (Even_ (Div (k_a ** prf_a))))          --Odd a = S a_
  (Odd_ (Even_ (Div (k_b ** prf_b))))          --= S Even = (k_a ** (k_a * 2 = a_))
  =                                            -- a_ Div 2
    Even_ (Div ( (S (k_a + k_b)) ** lemma))
    where
        lemma_refl_sum : {x, t, y, v: Nat} -> x = y -> t = v -> x + t = y + v
        lemma_refl_sum prf_x_y prf_t_v =
          rewrite prf_x_y in
          rewrite prf_t_v in
          Refl

        -- prf_a : k_a * 2 = a_
        -- prf_b : k_b * 2 = b_
        step_1 : (k_a + k_b) * 2 = a_ + b_
        step_1 =
          rewrite multDistributesOverPlusLeft k_a k_b 2 in -- from Idris Prelude.Nat и вынесли двоечку
          lemma_refl_sum prf_a prf_b -- k_a * 2 + k_b * 2 = a_ + b_

        step_2 : (k_a + k_b) * 2 = a_ + b_ -> 2 + (k_a + k_b) * 2 = 2 + (a_ + b_)
        step_2 prf = (re_out . re_out) prf

        step_3 : 2 + (k_a + k_b) * 2 = 2 + (a_ + b_) -> S (k_a + k_b) * 2 = S a_ + S b_
        step_3 prf =
          rewrite sym $ plusSuccRightSucc a_ b_ in
          prf

        lemma : S (k_a + k_b) * 2 = S a_ + S b_
        lemma = step_3 $ step_2 $ step_1

-- a: S a'
-- pf: q * 2 = a'
-- have: 2 + (q * 2) = 2 + a'
fromOddToEven : {a : Nat} -> Odd a -> Even (S a)
fromOddToEven {a = (S aa)} (Odd_ (Even_ (Div (k ** pf)))) =
    Even_ (Div ((S k) ** (re_out (re_out pf))))


checkEvenOrOdd : (a: Nat) -> Either (Odd a) (Even a)
checkEvenOrOdd Z = Right(Even_ (Div (Z ** Refl)))
checkEvenOrOdd (S k) = case checkEvenOrOdd k of
    Left odd_k => Right(fromOddToEven odd_k)
    Right even_k => Left(Odd_ even_k)


primeIsOdd : {a : Nat} -> Prime a -> a `GT` 2 -> Odd a
primeIsOdd {a} prime_a gt_a = case checkEvenOrOdd a of
    Left odd_a => odd_a
    Right even_a => absurd (evenNotPrime even_a gt_a prime_a)

--====================================================================================================================================================================
sumGt2IsGt2 : {a, b : Nat} -> a `GT` 2 -> b `GT` 2 -> (a + b) `GT` 2
sumGt2IsGt2  (LTESucc (LTESucc (LTESucc x))) (LTESucc (LTESucc (LTESucc y))) =
    LTESucc (LTESucc (LTESucc LTEZero))

sumPrimeIsNotPrime : {a, b : Nat} ->
            Prime a -> Prime b ->
            GT a 2 -> GT b 2 ->
            Prime (a + b) -> Void
sumPrimeIsNotPrime {a} {b} prime_a prime_b gt_a gt_b =
    evenNotPrime {a = a + b}
        (sumOddIsEven (primeIsOdd prime_a gt_a) (primeIsOdd prime_b gt_b))
        (sumGt2IsGt2 gt_a gt_b)
