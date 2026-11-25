/-
  RoutedInverseSums.lean

  Zero-dependency Lean 4 formal verification companion to:
  "Independently Routed Inverse Sums and Common-Rectangle Obstructions
   for Flat Unitary and Fourier Matrices"
  by Daniyar Kuttymbek, Adilkhan Kuttymbek, Dayana Kuttymbek,
  Amina Kolpenova, and Mukhammadali Kottumbekov.

  Uses Lean 4 core (`Init`) only -- no Mathlib or external dependencies required.
  Verify with: `lean RoutedInverseSums.lean`

  Contents:
    Part 1: Symbolic proofs for Theorems 1.1, 1.3, 2.1, and Lemmas 4.1-4.2 (zero `sorry`):
      - Theorem 2.1: Ordered strict half-separation cycle contradiction.
      - Lemma 4.1: Exact two-color 1/3-retention inequality for ALL u, a, b, plus
        sharpness for three equal (u/3, u/3) components.
      - Lemma 4.2: Sparse and diagonal elimination column-survival bound for ALL N, s, delta.
      - Theorem 1.1: Exact cutoff expansion B + 2c = d^2(qr+t)9^r + dq(3^r - 1) + 2(d - 1),
        non-circular legality 9q - 1 - q/2 >= 4q and d*R*3^(2r-j) >= 9q for ALL q, r >= 1,
        strict contradiction (N - c)^2 > N*B whenever N > B + 2c, and specializations
        (including q=2, r=2, s=1, t=1, delta=1 -> N <= 3697).
      - Theorem 1.3: Exact-field cell-pigeonhole bound N > delta0(r+1) + r(r+1)^r and r=2 -> 18.
    Part 2: Pure-kernel finite certificates (`decide` / `decide +kernel`, zero `native_decide`):
      - Lemma 6.1 exhaustive projective-direction verification across all 216 column-two
        3x3 matrices over F_2 and all 64 column-two 2x2 matrices over F_3 plus explicit
        row-degree-3 invertible column-two instances over F_3.
      - Lemma 3.1 swapped-complement nullity identity across all 256 subset pairs (I, J)
        on invertible 4x4 matrices over F_2 and F_5 (512 exact checks).
      - N = 4 over F_5 (omega = 2) consecutive-row Vandermonde nonvanishing vs.
        non-consecutive singular minor negative control ({0,2} x {0,2}).
      - Concrete legal-recurrence cutoff checks including (2, 2, 1, 1, 1) at N = 3698.
-/

namespace RoutedInverseSums

/-! ## Part 1: Symbolic Proofs -/

/-- Theorem 2.1: Ordered strict half-separation cycle impossibility. -/
theorem ordered_strict_separation_contradiction
    (maxA_lo minB_hi maxB_lo minA_hi : Nat)
    (h1 : maxA_lo ≥ minB_hi)
    (h2 : minB_hi > maxB_lo)
    (h3 : maxB_lo ≥ minA_hi)
    (h4 : minA_hi > maxA_lo) : False := by
  omega

/-- Lemma 4.1 (Two-color 1/3-retention): for ALL `u, a, b : Nat` with `a ≤ u`, `b ≤ u`,
    `2u ≤ 3(a + b) ≤ 4u`, at least one oriented cross pair `(a, u - b)` or `(u - a, b)`
    has both entries at least `u / 3` (in exact integer form `3 * x ≥ u`). -/
theorem two_color_third_retention (u a b : Nat)
    (ha : a ≤ u) (hb : b ≤ u)
    (hlo : 2 * u ≤ 3 * (a + b)) (hhi : 3 * (a + b) ≤ 4 * u) :
    (u ≤ 3 * a ∧ u ≤ 3 * (u - b)) ∨ (u ≤ 3 * (u - a) ∧ u ≤ 3 * b) := by
  omega

/-- Remark after Lemma 4.1: Sharpness of `1/3` for three `(k, k)` components (`u = 3k`). -/
theorem two_color_sharpness_3comp (k : Nat) :
    let u := 3 * k
    min k (u - k) = k ∧ min (u - k) k = k ∧
    min (2 * k) (u - 2 * k) = k ∧ min (u - 2 * k) (2 * k) = k := by
  dsimp only
  omega

/-- Lemma 4.2: Sparse and diagonal elimination leaves at least `p = N / d` columns. -/
theorem sparse_elimination_column_survival (N s delta : Nat) :
    let d := s + 1 + delta
    let p := N / d
    (d - 1) * p + p ≤ N := by
  dsimp only
  have hd : 1 ≤ s + 1 + delta := by omega
  have h1 : (s + 1 + delta - 1) * (N / (s + 1 + delta)) + N / (s + 1 + delta)
          = (s + 1 + delta) * (N / (s + 1 + delta)) := by
    have hsplit : (s + 1 + delta - 1) + 1 = s + 1 + delta := by omega
    calc (s + 1 + delta - 1) * (N / (s + 1 + delta)) + N / (s + 1 + delta)
      _ = (s + 1 + delta - 1) * (N / (s + 1 + delta)) + 1 * (N / (s + 1 + delta)) := by rw [Nat.one_mul]
      _ = ((s + 1 + delta - 1) + 1) * (N / (s + 1 + delta)) := (Nat.add_mul _ _ _).symm
      _ = (s + 1 + delta) * (N / (s + 1 + delta)) := by rw [hsplit]
  rw [h1]
  exact Nat.mul_div_le N (s + 1 + delta)

/-- Complex cutoff formula `N_cut(q, r, s, t, delta)` from Theorem 1.1, Eq. (1.4). -/
def complexCutoff (q r s t delta : Nat) : Nat :=
  let d := s + 1 + delta
  d * d * (q * r + t) * (9 ^ r) + d * q * (3 ^ r - 1) + 2 * (d - 1)

theorem three_pow_sq (r : Nat) : 3 ^ r * 3 ^ r = 9 ^ r := by
  induction r with
  | zero => rfl
  | succ k ih =>
    rw [Nat.pow_succ, Nat.pow_succ]
    calc 3 ^ k * 3 * (3 ^ k * 3) = (3 ^ k * 3 ^ k) * (3 * 3) := by ac_rfl
      _ = 9 ^ k * 9 := by rw [ih]

/-- Theorem 1.1: Exact cutoff decomposition `B + 2c = complexCutoff`, strict contradiction
    `(2N - 2c)^2 > 4NB` whenever `N > B + 2c`, and non-circular recurrence legality
    `d * R * 3^(2r - j) ≥ 9q` and `9q - 1 - q/2 ≥ 4q` for ALL `q, r ≥ 1`, `j < r`. -/
theorem complex_cutoff_contradiction_and_legality
    (q r s t delta N : Nat) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hN : complexCutoff q r s t delta < N) :
    let d := s + 1 + delta
    let R := q * r + t
    let a := 3 ^ r
    let c2 := 2 * (d - 1) + d * q * (a - 1)
    let B := d * d * R * (a * a)
    B + c2 = complexCutoff q r s t delta ∧
    c2 < 2 * N ∧
    4 * N * B < (2 * N - c2) * (2 * N - c2) ∧
    (∀ j, j < r → 9 * q ≤ d * R * 3 ^ (2 * r - j)) ∧
    8 * q ≤ 2 * (9 * q - 1) - q := by
  dsimp only
  have hsq : 3 ^ r * 3 ^ r = 9 ^ r := three_pow_sq r
  have hB : (s + 1 + delta) * (s + 1 + delta) * (q * r + t) * (3 ^ r * 3 ^ r) +
            (2 * (s + 1 + delta - 1) + (s + 1 + delta) * q * (3 ^ r - 1))
            = complexCutoff q r s t delta := by
    unfold complexCutoff
    dsimp only
    rw [hsq]
    omega
  have hc2_lt : 2 * (s + 1 + delta - 1) + (s + 1 + delta) * q * (3 ^ r - 1) < 2 * N := by
    omega
  have hstrict :
      4 * N * ((s + 1 + delta) * (s + 1 + delta) * (q * r + t) * (3 ^ r * 3 ^ r)) <
      (2 * N - (2 * (s + 1 + delta - 1) + (s + 1 + delta) * q * (3 ^ r - 1))) *
      (2 * N - (2 * (s + 1 + delta - 1) + (s + 1 + delta) * q * (3 ^ r - 1))) := by
    generalize hBdef : (s + 1 + delta) * (s + 1 + delta) * (q * r + t) * (3 ^ r * 3 ^ r) = B
    generalize hcdef : 2 * (s + 1 + delta - 1) + (s + 1 + delta) * q * (3 ^ r - 1) = c2
    rw [hBdef, hcdef] at hB
    rw [hcdef] at hc2_lt
    have hgt : B + c2 < N := by omega
    have hdiff_id : (2 * N - c2) * (2 * N - c2) = 4 * N * (N - c2) + c2 * c2 := by
      have hge : c2 ≤ N := by omega
      have h1 : (2 * N - c2) + c2 = 2 * N := by omega
      have hsq_add : ((2 * N - c2) + c2) * ((2 * N - c2) + c2)
                   = (2 * N - c2) * (2 * N - c2) + 2 * (2 * N - c2) * c2 + c2 * c2 := by
        rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
        have : c2 * (2 * N - c2) = (2 * N - c2) * c2 := Nat.mul_comm _ _
        have : 2 * (2 * N - c2) * c2 = (2 * N - c2) * c2 + (2 * N - c2) * c2 := by
          rw [Nat.two_mul, Nat.add_mul]
        omega
      rw [h1] at hsq_add
      have h2N : (2 * N) * (2 * N) = 4 * (N * N) := by
        calc 2 * N * (2 * N) = (2 * 2) * (N * N) := by ac_rfl
          _ = 4 * (N * N) := rfl
      have hmid : 2 * (2 * N - c2) * c2 = 4 * (N * c2) - 2 * (c2 * c2) := by
        have a : 2 * (2 * N - c2) = 4 * N - 2 * c2 := by omega
        rw [a, Nat.sub_mul]
        have b1 : 4 * N * c2 = 4 * (N * c2) := by ac_rfl
        have b2 : 2 * c2 * c2 = 2 * (c2 * c2) := by ac_rfl
        rw [b1, b2]
      have hNc : 4 * N * (N - c2) = 4 * (N * N) - 4 * (N * c2) := by
        rw [Nat.mul_sub]
        have b1 : 4 * N * N = 4 * (N * N) := by ac_rfl
        have b2 : 4 * N * c2 = 4 * (N * c2) := by ac_rfl
        rw [b1, b2]
      have hcc : c2 * c2 ≤ N * c2 := Nat.mul_le_mul_right c2 hge
      have hNN : N * c2 ≤ N * N := Nat.mul_le_mul_left N hge
      rw [h2N, hmid] at hsq_add
      rw [hNc]
      omega
    have hNB : 4 * N * B < 4 * N * (N - c2) := by
      have hpos : 0 < 4 * N := by omega
      exact Nat.mul_lt_mul_of_pos_left (by omega) hpos
    rw [hdiff_id]
    omega
  have hleg : ∀ j, j < r → 9 * q ≤ (s + 1 + delta) * (q * r + t) * 3 ^ (2 * r - j) := by
    intro j hj
    have hd1 : 1 ≤ s + 1 + delta := by omega
    have hRq : q ≤ q * r + t := by
      have : q * 1 ≤ q * r := Nat.mul_le_mul_left q hr
      omega
    have hexp : 2 ≤ 2 * r - j := by omega
    have h3pow : 9 ≤ 3 ^ (2 * r - j) := by
      have h1 : 3 ^ 2 ≤ 3 ^ (2 * r - j) := Nat.pow_le_pow_right (by omega) hexp
      exact h1
    have hmul1 : q * 9 ≤ (q * r + t) * 3 ^ (2 * r - j) := Nat.mul_le_mul hRq h3pow
    have hmul2 : 1 * (q * 9) ≤ (s + 1 + delta) * ((q * r + t) * 3 ^ (2 * r - j)) :=
      Nat.mul_le_mul hd1 hmul1
    have hassoc : (s + 1 + delta) * ((q * r + t) * 3 ^ (2 * r - j))
                = (s + 1 + delta) * (q * r + t) * 3 ^ (2 * r - j) := by ac_rfl
    rw [hassoc] at hmul2
    omega
  refine ⟨hB, hc2_lt, hstrict, hleg, by omega⟩

/-- Remark 4.3: Base specializations and the numerical example `N ≤ 3697`. -/
theorem complex_cutoff_specializations (q r : Nat) :
    complexCutoff q r 0 0 0 = q * r * 9 ^ r + q * (3 ^ r - 1) ∧
    complexCutoff q r 0 0 1 = 4 * (q * r) * 9 ^ r + 2 * q * (3 ^ r - 1) + 2 ∧
    complexCutoff 2 2 1 1 1 = 3697 := by
  refine ⟨?_, ?_, by decide⟩
  · unfold complexCutoff; simp
  · unfold complexCutoff
    dsimp only
    have h1 : 0 + 1 + 1 = 2 := rfl
    have h2 : 2 * 2 * (q * r + 0) * 9 ^ r = 4 * (q * r) * 9 ^ r := by simp
    rw [h1, h2]

/-- Theorem 1.3: Exact-field cell-pigeonhole bound and `r = 2, delta0 = 0` cutoff (`N ≤ 18`). -/
theorem exact_field_cell_pigeonhole (N r delta0 : Nat)
    (hN : delta0 * (r + 1) + r * (r + 1) ^ r < N) :
    r * (r + 1) ^ r < N - delta0 * (r + 1) := by
  omega

theorem exact_field_r2_cutoff : 0 * (2 + 1) + 2 * (2 + 1) ^ 2 = 18 := rfl

/-! ## Part 2: Pure-Kernel Finite Certificates (`decide` / `decide +kernel`, zero `native_decide`) -/

def powMod (a n p : Nat) : Nat :=
  let rec go (fuel base exp acc : Nat) : Nat :=
    match fuel with
    | 0 => acc
    | f + 1 =>
      if exp == 0 then acc
      else
        let acc' := if exp % 2 == 1 then (acc * base) % p else acc
        go f ((base * base) % p) (exp / 2) acc'
  go 16 (a % p) n 1

/-- Exact matrix rank over `F_p` (structural fold, kernel-reducible). -/
def rankMod (p ncols : Nat) (rows : List (List Nat)) : Nat :=
  let (_, rk) := (List.range ncols).foldl (fun (rem, rk) col =>
    match rem.findIdx? (fun r => r.getD col 0 % p != 0) with
    | none => (rem, rk)
    | some pidx =>
      let pivRow := rem.getD pidx []
      let invP := powMod (pivRow.getD col 0) (p - 2) p
      let normPiv := (List.range ncols).map fun j => (pivRow.getD j 0 * invP) % p
      let others := (rem.take pidx) ++ (rem.drop (pidx + 1))
      let reduced := others.map fun r =>
        let fac := r.getD col 0 % p
        if fac == 0 then r
        else (List.range ncols).map fun j =>
          (r.getD j 0 + p - (fac * normPiv.getD j 0) % p) % p
      (reduced, rk + 1)) (rows, 0)
  rk

/-- Exact Gauss-Jordan matrix inverse over `F_p` (returns `none` if singular). -/
def invMod (p n : Nat) (mat : List (List Nat)) : Option (List (List Nat)) :=
  let aug0 := (List.range n).map fun i =>
    let row := mat.getD i []
    (List.range n).map (fun j => row.getD j 0 % p) ++
    (List.range n).map (fun j => if i == j then 1 else 0)
  let res := (List.range n).foldl (fun accOpt col =>
    match accOpt with
    | none => none
    | some aug =>
      let tail := aug.drop col
      match tail.findIdx? (fun r => r.getD col 0 % p != 0) with
      | none => none
      | some off =>
        let pidx := col + off
        let rCol := aug.getD col []
        let rPiv := aug.getD pidx []
        let swapped := (List.range n).map fun i =>
          if i == col then rPiv else if i == pidx then rCol else aug.getD i []
        let invP := powMod (rPiv.getD col 0) (p - 2) p
        let normRow := rPiv.map fun v => (v * invP) % p
        let elim := (List.range n).map fun i =>
          if i == col then normRow
          else
            let r := swapped.getD i []
            let fac := r.getD col 0 % p
            if fac == 0 then r
            else (List.range (2 * n)).map fun j =>
              (r.getD j 0 + p - (fac * normRow.getD j 0) % p) % p
        some elim) (some aug0)
  res.map (fun aug => aug.map (fun r => r.drop n))

def normalizeProj (p : Nat) (vec : List Nat) : Option (List Nat) :=
  match vec.find? (· % p != 0) with
  | none => none
  | some v =>
    let iv := powMod v (p - 2) p
    some (vec.map fun x => (x * iv) % p)

def dedupList (xs : List (List Nat)) : List (List Nat) :=
  xs.foldl (fun acc x => if acc.contains x then acc else x :: acc) []

def nonemptySubsets (n : Nat) : List (List Nat) :=
  ((List.range (2 ^ n)).drop 1).map fun mask =>
    (List.range n).filter fun i => (mask / (2 ^ i)) % 2 == 1

def checkCol2Matrix (p n : Nat) (Q : List (List Nat)) : Bool × Bool :=
  match invMod p n Q with
  | none => (false, true)
  | some Qinv =>
    let ok := (nonemptySubsets n).all fun J =>
      let k := J.length
      let dirs := dedupList <| (List.range n).filterMap fun c =>
        normalizeProj p (J.map fun r => (Qinv.getD r []).getD c 0)
      dirs.length == k && rankMod p k dirs == k
    (true, ok)

def col2ColsF2_3 : List (List Nat) :=
  [[1,0,0], [0,1,0], [0,0,1], [1,1,0], [1,0,1], [0,1,1]]

def checkAllCol2_F2_N3 : Nat × Bool :=
  let cols := col2ColsF2_3
  cols.foldl (fun st c0 =>
    cols.foldl (fun st1 c1 =>
      cols.foldl (fun (invCnt, ok) c2 =>
        let Q := (List.range 3).map fun r => [c0.getD r 0, c1.getD r 0, c2.getD r 0]
        let (isInv, pass) := checkCol2Matrix 2 3 Q
        (invCnt + (if isInv then 1 else 0), ok && pass)) st1) st) (0, true)

def col2ColsF3_2 : List (List Nat) :=
  [[1,0], [2,0], [0,1], [0,2], [1,1], [1,2], [2,1], [2,2]]

def checkAllCol2_F3_N2 : Nat × Bool :=
  let cols := col2ColsF3_2
  cols.foldl (fun st c0 =>
    cols.foldl (fun (invCnt, ok) c1 =>
      let Q := (List.range 2).map fun r => [c0.getD r 0, c1.getD r 0]
      let (isInv, pass) := checkCol2Matrix 3 2 Q
      (invCnt + (if isInv then 1 else 0), ok && pass)) st) (0, true)

/-- Pure-kernel verification of Lemma 6.1 across all 216 column-two 3×3 matrices over `F_2`
    (96 invertible), all 64 column-two 2×2 matrices over `F_3` (48 invertible), and an
    invertible row-degree-3 column-two 3×3 matrix over `F_3`. -/
theorem exhaustive_col2_proj_dirs_F2_F3 :
    checkAllCol2_F2_N3 = (96, true) ∧
    checkAllCol2_F3_N2 = (48, true) ∧
    checkCol2Matrix 3 3 [[1, 1, 1], [1, 0, 2], [0, 1, 0]] = (true, true) := by
  decide +kernel

def allSubsets (n : Nat) : List (List Nat) :=
  (List.range (2 ^ n)).map fun mask =>
    (List.range n).filter fun i => (mask / (2 ^ i)) % 2 == 1

def checkNullityAll256 (p : Nat) (A : List (List Nat)) : Bool :=
  match invMod p 4 A with
  | none => false
  | some Ainv =>
    let subs := allSubsets 4
    subs.all fun I =>
      let Ic := (List.range 4).filter (fun x => !I.contains x)
      subs.all fun J =>
        let Jc := (List.range 4).filter (fun x => !J.contains x)
        let sub1 := I.map fun i => J.map fun j => (Ainv.getD i []).getD j 0
        let sub2 := Jc.map fun j => Ic.map fun i => (A.getD j []).getD i 0
        let r1 : Int := (rankMod p J.length sub1 : Int)
        let r2 : Int := (rankMod p Ic.length sub2 : Int)
        r1 == r2 + (I.length : Int) + (J.length : Int) - 4

/-- Pure-kernel verification of Lemma 3.1 (swapped-complement nullity identity) across
    all `16 × 16 = 256` subset pairs on invertible `4×4` matrices over `F_2` and `F_5`. -/
theorem swapped_complement_nullity_F2_F5 :
    checkNullityAll256 2 [[1,1,0,0], [0,1,1,0], [0,0,1,1], [1,0,0,0]] = true ∧
    checkNullityAll256 5 [[2,1,0,3], [0,4,2,1], [3,0,1,4], [1,2,3,0]] = true := by
  decide +kernel

/-- Pure-kernel verification of consecutive-row Vandermonde nonvanishing vs. non-consecutive
    singular minor (`rows = {0,2}, cols = {0,2}`) for `F_4` over `F_5` (`ω = 2`). -/
def checkF4overF5 : Bool :=
  let F := (List.range 4).map fun a => (List.range 4).map fun b => powMod 2 (a * b) 5
  let subs := nonemptySubsets 4
  let consecOk := (List.range 4).all fun start =>
    subs.all fun cols =>
      let k := cols.length
      let rows := (List.range k).map fun j => (start + j) % 4
      let sub := rows.map fun r => cols.map fun c => (F.getD r []).getD c 0
      rankMod 5 k sub == k
  let badSub := [0, 2].map fun r => [0, 2].map fun c => (F.getD r []).getD c 0
  consecOk && rankMod 5 2 badSub == 1

theorem vandermonde_F5_consecutive_vs_nonconsecutive : checkF4overF5 = true := by
  decide +kernel

/-- Pure-kernel check of recurrence legality and strict final contradiction `m_r^2 > N * R`
    at `N = complexCutoff + 1` across concrete parameter tuples (including `N = 3698`). -/
def checkConcreteCutoff (q r s t delta : Nat) : Bool :=
  let d := s + 1 + delta
  let N := complexCutoff q r s t delta + 1
  let (mFinal, legal) := (List.range r).foldl (fun (m, ok) _ =>
    ((m - q + 2) / 3, ok && m ≥ 4 * q)) (N / d, true)
  legal && mFinal * mFinal > N * (q * r + t)

theorem concrete_legal_recurrence_cutoffs :
    checkConcreteCutoff 1 1 0 0 0 = true ∧
    checkConcreteCutoff 2 1 0 0 1 = true ∧
    checkConcreteCutoff 2 2 0 0 0 = true ∧
    checkConcreteCutoff 2 2 1 1 1 = true ∧
    checkConcreteCutoff 3 2 2 1 1 = true := by
  decide

end RoutedInverseSums
