%default total

sumn : (n : Nat) -> Nat
sumn Z = Z
sumn (S k) = (S k) + sumn k

congs : (f : t -> u) -> (a = b) -> f a = f b
congs f Refl = Refl

lemmochka : {a, b: Nat} -> (c : Nat) -> a = b -> a + c = b + c
lemmochka {a} {b} c prf = rewrite plusCommutative a c in
    rewrite plusCommutative b c in congs (plus c) prf

step_1 : {k : Nat} -> 2 * sumn k = k * (S k) ->
                      2 * sumn k + 2 * (S k) = k * (S k) + 2 * (S k)
step_1 {k} prf = lemmochka (2 * (S k)) prf

step_2 : {k : Nat} -> 2 * sumn k + 2 * (S k)     = k * (S k) + 2 * (S k) ->
                      2 * (sumn k + (S k))       = k * (S k) + 2 * (S k)
step_2 {k} prf =
    rewrite (lll k) in prf
    where
        lll : (k : Nat) -> 2 * (sumn k + (S k)) =  2 * sumn k + 2 * (S k)
        lll k = rewrite sym $ multDistributesOverPlusRight 2 (sumn k) (S k) in Refl

step_3 : {k : Nat} -> 2 * (sumn k + (S k)) = k * (S k) + 2 * (S k) ->
                      2 * (sumn k + (S k)) = (S (S k)) * (S k)
step_3 {k} prf =
    rewrite sym $ lll k in prf
    where
        lll : (k : Nat) -> k * (S k) + 2 * (S k) =  (S (S k)) * (S k)
        lll k = rewrite sym $ multDistributesOverPlusLeft k 2 (S k) in
                rewrite plusCommutative k 2 in Refl

step_4 : {k : Nat} -> 2 * (sumn k + (S k)) = (S (S k)) * (S k) ->
                      2 * (sumn (S k))     = (S (S k)) * (S k)
step_4 {k} prf = rewrite (sym $ lll k) in prf
    where
        lll : (k : Nat) -> 2 * (sumn k + (S k)) = 2 * (sumn (S k))
        lll k = rewrite (plusCommutative (sumn k) (S k)) in Refl

-- step_4
lemma_induct_step : {n : Nat} -> 2 * sumn n = n * (S n) -> 2 * (sumn (S n)) = (S n) * (S (S n))
lemma_induct_step {n} refl =
    rewrite multCommutative (S n) (S (S n)) in
    step_4 $ step_3 $ step_2 $ step_1 refl

proof_formula_modified : (n : Nat) -> 2 * sumn n = n * (S n)
proof_formula_modified Z = Refl
proof_formula_modified (S k) = lemma_induct_step (proof_formula_modified k)
