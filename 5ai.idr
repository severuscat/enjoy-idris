%default total

data DividesNat : (a : Nat) -> (b : Nat) -> Type where
    Div : (k ** (k * x = y)) -> DividesNat y x

data Prime : (p : Nat) -> Type where
    ConsPrime : LTE 2 p ->
        ((d : Nat) -> DividesNat p d -> Either (d = 1) (d = p)) ->
        Prime p

data Theorem : (a : Nat) -> (b : Nat) -> Type where
    ThStatement : {a, b: Nat} ->
        (Prime a) -> (Prime b) -> (c = a + b) -> (Prime c) ->
        Theorem a b

disjoint : {n : Nat} -> Z = S n -> Void
disjoint {n} p = replace {P = disjointTy} p ()
    where
        disjointTy : Nat -> Type
        disjointTy Z = ()
        disjointTy (S k) = Void

out : S a = S b -> a = b
out Refl = Refl

mulZIsZ : {k : Nat} -> k * Z = Z
mulZIsZ {k} = rewrite (multCommutative k Z) in Refl

zeroIsNotDiv : (k ** (k * Z = (S a))) -> Void
zeroIsNotDiv (k ** pf) = disjoint $ sym $ trans (sym pf) mulZIsZ

kMul2Eq1 : {k : Nat} -> (k ** (k * (S (S Z)) = (S Z))) -> Void
kMul2Eq1 {k = Z} (x ** pf) = disjoint pf
kMul2Eq1 {k = (S Z)} (x ** pf) = disjoint $ out $ sym pf
kMul2Eq1 {k = (S (S a))} (x ** pf) = disjoint $ out $ sym pf

plusNotChangeGT : {a, b, c: Nat} -> a `GT` c -> a + b `GT` c
plusNotChangeGT {a = (S right)} {b = b} {c = Z} (LTESucc  LTEZero) = LTESucc LTEZero
plusNotChangeGT {a = (S (S k))} {b = b} {c = (S left)} (LTESucc (LTESucc x)) = LTESucc $ plusNotChangeGT (LTESucc x)
plusNotChangeGT {a = Z} {b = _} LTEZero impossible
plusNotChangeGT {a = Z} {b = _} (LTESucc _) impossible
plusNotChangeGT {a = (S Z)} {b = _} {c = (S _)} (LTESucc LTEZero) impossible
plusNotChangeGT {a = (S Z)} {b = _} {c = (S _)} (LTESucc (LTESucc _)) impossible

gtNotRefl : {a, b: Nat} -> a `GT` b -> a = b -> Void
gtNotRefl {a = Z} {b = _} LTEZero _ impossible
gtNotRefl {a = Z} {b = _} (LTESucc _) _ impossible
gtNotRefl {a = (S k)} {b = Z} (LTESucc x) prf = disjoint $ sym prf
gtNotRefl {a = (S k)} {b = (S j)} (LTESucc x) prf =
    gtNotRefl x (out prf)

notGtABMulAKEqB : {k : Nat} -> (x : Nat) -> (y : Nat) -> x `GT` (S y) -> (k * x = (S y)) -> Void
notGtABMulAKEqB {k = Z} _ _ _ Refl impossible
notGtABMulAKEqB {k = (S k)} x y gtXY prf =
    gtNotRefl (plusNotChangeGT {a = x} {b = k * x} {c = S y} gtXY) prf

gtIsNotDiv : {x, y : Nat} -> x `GT` (S y) -> (k ** (k * x = (S y))) -> Void
gtIsNotDiv {x = Z} {y = _} LTEZero _ impossible
gtIsNotDiv {x = Z} {y = _} (LTESucc _) _ impossible
gtIsNotDiv {x = (S Z)} {y = _} (LTESucc LTEZero) _ impossible
gtIsNotDiv {x = (S Z)} {y = _} (LTESucc (LTESucc _)) _ impossible
gtIsNotDiv {x = (S (S Z))} {y = Z} (LTESucc (LTESucc LTEZero)) (k ** pf) =
    absurd (kMul2Eq1 (k ** pf))
gtIsNotDiv {x = (S (S Z))} {y = (S _)} (LTESucc (LTESucc LTEZero)) _ impossible
gtIsNotDiv {x = (S (S Z))} {y = (S _)} (LTESucc (LTESucc (LTESucc _))) _ impossible
gtIsNotDiv {x = (S (S (S p)))} {y = (S j)} gt (k ** pf) =
    notGtABMulAKEqB (S (S ( S p))) (S j) gt pf
gtIsNotDiv {x = (S (S (S p)))} {y = Z} gt (k ** pf) =
     notGtABMulAKEqB (S (S ( S p))) Z gt pf

prf2IsPrime : Prime (S (S Z))
prf2IsPrime = ConsPrime (LTESucc (LTESucc LTEZero)) prf
    where
        prfGT32 : (S (S (S a))) `GT` (S (S Z))
        prfGT32 = LTESucc (LTESucc (LTESucc LTEZero))

        prf : (d : Nat) -> DividesNat (S (S Z)) d -> Either (d = 1) (d = (S (S Z)))
        prf Z (Div (x ** pf)) = absurd (zeroIsNotDiv (x ** pf))
        prf (S Z) (Div (x ** pf)) = Left Refl
        prf (S (S Z)) (Div (x ** pf)) = Right Refl
        prf (S (S (S _))) (Div (k ** pf)) =
            absurd (gtIsNotDiv prfGT32 (k ** pf))

notDivides32 : {k : Nat} -> (k ** (k * (S (S Z)) = (S (S (S Z))))) -> Void
notDivides32 {k = Z} (x ** pf) = disjoint pf
notDivides32 {k = (S Z)} (x ** pf) = disjoint $ out $ out pf
notDivides32 {k = (S (S _))} (x ** pf) = disjoint $ out $ out $ out $ sym pf

notDivides52 : {k : Nat} -> (k ** (k * (S (S Z))) = (S (S (S (S (S Z)))))) -> Void
notDivides52 {k = Z} (x ** pf) = disjoint pf
notDivides52 {k = (S Z)} (x ** pf) = disjoint $ out $ out pf
notDivides52 {k = (S (S Z))} (x ** pf) = disjoint $ out $ out $ out $ out pf
notDivides52 {k = (S (S (S _)))} (x ** pf) = disjoint $ out $ out $ out $ out $ out $ sym pf

notDivides53 : {k : Nat} -> (k ** (k * (S (S (S Z)))) = (S (S (S (S (S Z)))))) -> Void
notDivides53 {k = Z} (x ** pf) = disjoint pf
notDivides53 {k = (S Z)} (x ** pf) = disjoint $ out $ out $ out pf
notDivides53 {k = (S (S _))} (x ** pf) = disjoint $ out $ out $ out $ out $ out $ sym pf

notDivides54 : {k : Nat} -> (k ** (k * (S (S (S (S Z))))) = (S (S (S (S (S Z)))))) -> Void
notDivides54 {k = Z} (x ** pf) = disjoint pf
notDivides54 {k = (S Z)} (x ** pf) = disjoint $ out $ out $ out $ out pf
notDivides54 {k = (S (S _))} (x ** pf) = disjoint $ out $ out $ out $ out $ out $ sym pf

prf3IsPrime : Prime (S (S (S Z)))
prf3IsPrime = ConsPrime (LTESucc (LTESucc LTEZero)) prf
    where
        prfGT43 : (S (S (S (S a)))) `GT` (S (S (S Z)))
        prfGT43 = LTESucc (LTESucc (LTESucc (LTESucc LTEZero)))

        prf : (d : Nat) -> DividesNat (S (S (S Z))) d -> Either (d = 1) (d = (S (S (S Z))))
        prf Z (Div (x ** pf)) = absurd (zeroIsNotDiv (x ** pf))
        prf (S Z) x = Left Refl
        prf (S (S Z)) (Div (k ** pf)) = absurd (notDivides32 (k ** pf))
        prf (S (S (S Z))) x = Right Refl
        prf (S (S (S (S _)))) (Div (x ** pf)) = absurd (gtIsNotDiv (prfGT43) (x ** pf))

prf5IsPrime : Prime (S (S (S (S (S Z)))))
prf5IsPrime = ConsPrime (LTESucc (LTESucc LTEZero)) prf
    where
        prfGT65 : (S (S (S (S (S (S a)))))) `GT` (S (S (S (S (S Z)))))
        prfGT65 = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc LTEZero)))))

        prf : (d : Nat) -> DividesNat (S (S (S (S (S Z))))) d ->
              Either (d = 1) (d = (S (S (S (S (S Z))))))
        prf Z (Div (x ** pf)) = absurd (zeroIsNotDiv (x ** pf))
        prf (S Z) x = Left Refl
        prf (S (S Z)) (Div (k ** pf)) = absurd (notDivides52 (k ** pf))
        prf (S (S (S Z))) (Div (k ** pf)) = absurd (notDivides53 (k ** pf))
        prf (S (S (S (S Z)))) (Div (k ** pf)) = absurd (notDivides54 (k ** pf))
        prf (S (S (S (S (S Z))))) x = Right Refl
        prf (S (S (S (S (S (S _)))))) (Div (x ** pf)) = absurd (gtIsNotDiv (prfGT65) (x ** pf))


prfRefl5 : ((S (S Z)) + (S (S (S Z))) = (S (S (S (S (S Z))))))
prfRefl5 = Refl

theorem : Theorem (S (S Z)) (S (S (S Z)))
theorem = ThStatement {c = S (S (S (S (S Z))))}
        prf2IsPrime
        prf3IsPrime
        prfRefl5
        prf5IsPrime
