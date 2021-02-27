import topology.instances.real

namespace real

theorem Inf_le_Sup (S : set ℝ) (h₁ : ∃ x, x ∈ S) (h₂ : ∃ x, ∀ y ∈ S, y ≤ x) 
  (h₃ : ∃ x, ∀ y ∈ S, x ≤ y) :
  Inf S ≤ Sup S :=
begin
  cases h₁ with k hk,
  exact le_trans (real.Inf_le _ h₃ hk) (real.le_Sup _ h₂ hk),
end

end real

lemma exists_of_range_eq_range {α : Type*} [linear_order α] {f g : ℕ → α} 
  (hfg : set.range f = set.range g) (n : ℕ) : 
  ∃ k, f n = g k :=
begin
  have h₁ : f n ∈ set.range g,
  { simp [←hfg] },
  rcases h₁ with ⟨t, ht⟩,
  use t, rw ht
end

lemma eq_of_strict_mono_of_range_eq {α : Type*} [linear_order α] {f g : ℕ → α} (hf : strict_mono f) 
  (hg : strict_mono g) (hfg : set.range f = set.range g) : f = g :=
begin
  ext i,
  apply nat.strong_induction_on i,
  clear i,
  intros i ih,
  by_contra h,
  cases ne.lt_or_lt h with h₁ h₁,
  { cases exists_of_range_eq_range hfg i with m hm,
    have hmi : m < i,
    { rwa [hm, hg.lt_iff_lt] at h₁ },
    specialize ih m hmi,
    rwa [←hf.lt_iff_lt, hm, ih] at hmi,
    exact lt_irrefl _ hmi },
  { cases exists_of_range_eq_range hfg.symm i with m hm,
    have hmi : m < i,
    { rwa [hm, hf.lt_iff_lt] at h₁ },
    specialize ih m hmi,
    rwa [←hg.lt_iff_lt, hm, ih] at hmi,
    exact lt_irrefl _ hmi }
end

def bounded_within (f : ℝ → ℝ) (a b : ℝ) := ∃ k, ∀ x ∈ set.Icc a b, abs (f x) < k
