import .missing

open_locale big_operators

noncomputable theory

/-!
# Darboux Integrals in Lean

In this file, we formalise the theory of Darboux integrals in Lean. Although more general integrals,
that is, the Lebesgue and Bochner Integrals have been formalised already, the Darboux Integral has
not been formalised yet.
-/

/-!
## Dissections

We start off with the definition of a dissection (or partition) of a closed interval [a, b]. Note
that to make definitions simpler, we only assume strict monotonicity, and that x₀ = a, xₙ = b. This
means that the behaviour outside of [0, n] is undefined.
-/

/--
A dissection (or partition) of [a, b] is the sequence a = x₀ < x₁ < ... < xₙ = b
(Note in this case, we allow xₖ where k > n, and this is simply undefined) 
-/
@[ext]
structure dissection (a b : ℝ) :=
(x : ℕ → ℝ)
(n : ℕ)
(mono : strict_mono x)
(hx0 : x 0 = a)
(hxn : x n = b)

namespace dissection

variables {a b : ℝ}

lemma eq_of_x_eq {D D' : dissection a b} (h : D.x = D'.x) : D = D' :=
begin
  ext,
  { rw h },
  have h₁ := D.hxn,
  have h₂ := D'.hxn,
  simp_rw [←h₂, h] at h₁,
  exact D'.mono.injective h₁,
end

/-!
## Darboux Sums

With Dissections defined, we can use them to define Darboux Sums. In this instance, we do not
require the functions to be bounded. This means that the Sup and Inf are not guaranteed to exist,
however, it makes more sense to take in the assumption that the function is bounded later on,
instead of passing it into the definition where it is never used.
-/

/--
The lower Darboux sum
-/
def lower_sum (D : dissection a b) (f : ℝ → ℝ) : ℝ :=
∑ i in finset.range D.n, (D.x (i+1) - D.x i) * Inf (f '' set.Icc (D.x i) (D.x (i + 1)))

/--
The upper Darboux Sum
-/
def upper_sum (D : dissection a b) (f : ℝ → ℝ) : ℝ :=
∑ i in finset.range D.n, (D.x (i+1) - D.x i) * Sup (f '' set.Icc (D.x i) (D.x (i + 1)))

lemma a_le_x (D : dissection a b) (n : ℕ) : a ≤ D.x n :=
begin
  simp_rw [←D.hx0, D.mono.le_iff_le],
  exact nat.zero_le _,
end

lemma x_le_b (D : dissection a b) (i : ℕ) (hi : i ≤ D.n) : D.x i ≤ b :=
begin
  simp_rw [←D.hxn, D.mono.le_iff_le],
  exact hi
end

/--
We can show that for any bounded function f, the lower Darboux sum is less than or equal to the 
upper Darboux sum
-/
lemma lower_sum_le_upper_sum (D : dissection a b) {f : ℝ → ℝ} {k : ℝ} (hf : bounded_within f a b) :
  D.lower_sum f ≤ D.upper_sum f :=
begin
  unfold lower_sum upper_sum,
  apply finset.sum_le_sum,
  rcases hf with ⟨k, hf⟩,
  intros i hi,
  rw finset.mem_range at hi,
  rw mul_le_mul_left,
  { apply real.Inf_le_Sup,
    { use [f (D.x i), D.x i],
      exact ⟨⟨le_refl _, (D.mono i.lt_succ_self).le⟩, rfl⟩ },
    { use k,
      rintros y ⟨x, hx, rfl⟩,
      have xab : x ∈ set.Icc a b := set.Icc_subset_Icc (a_le_x _ _) (x_le_b _ _ hi) hx,
      specialize hf x xab,
      rw abs_lt at hf,
      exact hf.2.le },
    { use -k,
      rintros y ⟨x, hx, rfl⟩,
      have xab : x ∈ set.Icc a b := set.Icc_subset_Icc (a_le_x _ _) (x_le_b _ _ hi) hx,
      specialize hf x xab,
      rw abs_lt at hf,
      exact hf.1.le } },
  { rw sub_pos,
    apply D.mono,
    exact i.lt_succ_self }
end

/--
As we did not define a dissection as a set, the definition of a dissection being a refinement of
another is slightly different.

We can say D ≤ D' to mean D ⊆ D', which in this case means that D' is a refinement of D, In
particular, every point in D is in D'.
-/
instance : partial_order (dissection a b) :=
{ le := λ D D', ∀ i, ∃ j, D.x i = D'.x j,
  le_refl := 
  begin
    intros D i,
    use i,
  end,
  le_trans := 
  begin
    intros D D' D'' h₁ h₂ i,
    cases h₁ i with j hj,
    cases h₂ j with k hk,
    use k,
    rw [hj, hk]
  end,
  le_antisymm :=
  begin
    intros D D' h₁ h₂,
    have h₃ : set.range D.x = set.range D'.x,
    { apply set.subset.antisymm,
      { rintros y ⟨t, ht⟩,
        cases h₁ t,
        use w,
        rw [←ht, h] },
      { rintros y ⟨t, ht⟩,
        cases h₂ t,
        use w,
        rw [←ht, h] } },
    have h₄ := eq_of_strict_mono_of_range_eq D.mono D'.mono h₃,
    exact eq_of_x_eq h₄,
  end }

/-!
Now, we can show that if D' is a refinement of D, then

D.lower_sum ≤ D'.lower_sum ≤ D'.upper_sum ≤ D.upper_sum

With this, we can take the Inf of all of the upper sums, as the set of all upper sums is bounded
below. In addition, we can take the Sup of the lower sums.
-/
lemma upper_sum_mono {f : ℝ → ℝ} (hf : bounded_within f a b) (D D' : dissection a b) 
  (h : D ≤ D') : D'.upper_sum ≤ D.upper_sum :=
begin
  sorry
end

lemma lower_sum_mono {f : ℝ → ℝ} (hf : bounded_within f a b) (D D' : dissection a b) 
  (h : D ≤ D') : D.lower_sum ≤ D'.lower_sum :=
begin
  sorry
end

-- Todo: flesh out ≤ API
-- Todo: define the dissection D ∪ D', as it's useful for a few proofs
end dissection

section integrals

variables (f : ℝ → ℝ) (a b : ℝ)

/-!
# Lower and Upper Integrals

We can now define the Lower and Upper Integrals, by taking the Sup/Inf as appropriate. Note here
that we do not require f to be bounded in the definition, instead we take the approach of totalising
these, and allowing for junk output for unbounded functions
-/
def lower_integral : ℝ := Sup { x | ∃ D : dissection a b, D.lower_sum f = x }
def upper_integral : ℝ := Inf { x | ∃ D : dissection a b, D.upper_sum f = x }

/-!
# Integrable

Finally, we can define what it means for a function to be integrable. We say that a function f is
Darboux Integrable if the lower and upper integrals are the same.
-/
def integrable : Prop := lower_integral f a b = upper_integral f a b

end integrals

section integrable

variables {a b : ℝ}

/-- 
Any monotone function is integrable. Note here `monotone` means monotonically increasing.
-/
lemma integrable_of_monotone_of_bounded {f : ℝ → ℝ} (hfm : monotone f) 
  (hfb : bounded_within f a b) : integrable f a b := sorry

/--
Any continouous function is integrable.
-/
lemma integrable_of_continuous_of_bounded {f : ℝ → ℝ} (hfm : monotone f) 
  (hfb : bounded_within f a b) : integrable f a b := sorry

lemma integrable.const (c : ℝ) : integrable (λ x, c) a b := sorry

lemma integrable.add {f g : ℝ → ℝ} (hf : integrable f a b) (hg : integrable g a b) :
  integrable (f + g) a b := sorry

lemma integrable.abs {f g : ℝ → ℝ} (hf : integrable f a b) : integrable (abs ∘ f) a b := sorry

lemma integrable.mul {f g : ℝ → ℝ} (hf : integrable f a b) (hg : integrable g a b) :
  integrable (f * g) a b := sorry

end integrable
