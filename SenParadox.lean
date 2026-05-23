import Mathlib

-- Formalisation of economic theory
-- Sen's Impossibility of a Paretian Liberal (1970)

-- §1: Defining Basic Types
def PreferenceRelation (Alt : Type*) := Alt → Alt → Prop

-- §2: Defining what makes a preference relation an ordering
structure IsWeakOrder (R : PreferenceRelation Alt) : Prop where
  refl  : ∀ x : Alt, R x x
  trans : ∀ x y z : Alt, R x y → R y z → R x z
  total : ∀ x y : Alt, R x y ∨ R y x

-- §3: Defining the profile
def Profile (Individual : Type*) (Alt : Type*) :=
  Individual → PreferenceRelation Alt

-- §4: Defining the Collective Choice Rule (CCR)
def CCR (Individual : Type*) (Alt : Type*) :=
  Profile Individual Alt → PreferenceRelation Alt

-- §7: Social Welfare Function (SWF)
def SWF {Individual : Type*} {Alt : Type*} (f : CCR Individual Alt) : Prop :=
  ∀ (p : Profile Individual Alt), IsWeakOrder (Alt := Alt) (f p)

-- §8: Choice Function
def GeneratesChoiceFunction (R : PreferenceRelation Alt) : Prop :=
  ∀ (S : Finset Alt), S.Nonempty →
    ∃ x ∈ S, ∀ y ∈ S, R x y

-- §9: Social Decision Function (SDF)
def SDF {Individual : Type*} {Alt : Type*} (f : CCR Individual Alt) : Prop :=
  ∀ (p : Profile Individual Alt), GeneratesChoiceFunction (Alt := Alt) (f p)

-- §10: Condition U - Unrestricted Domain
def ConditionU (_f : CCR Individual Alt) : Prop := True

-- §11: Condition P - Pareto Principle
def ConditionP (f : CCR Individual Alt) : Prop :=
  ∀ (p : Profile Individual Alt) (x y : Alt),
    (∀ i : Individual, p i x y ∧ ¬ p i y x) →
    (f p x y ∧ ¬ f p y x)

-- §12: Condition L - Liberalism
def ConditionL (f : CCR Individual Alt) : Prop :=
  ∀ i : Individual, ∃ x y : Alt, x ≠ y ∧
    ∀ (p : Profile Individual Alt),
      (p i x y ∧ ¬ p i y x → f p x y ∧ ¬ f p y x) ∧
      (p i y x ∧ ¬ p i x y → f p y x ∧ ¬ f p x y)

-- §13: Condition L* - Minimal Liberalism
def ConditionL' (f : CCR Individual Alt) : Prop :=
  ∃ i j : Individual, i ≠ j ∧
    (∃ x y : Alt, x ≠ y ∧
      ∀ (p : Profile Individual Alt),
        (p i x y ∧ ¬ p i y x → f p x y ∧ ¬ f p y x) ∧
        (p i y x ∧ ¬ p i x y → f p y x ∧ ¬ f p x y)) ∧
    (∃ x y : Alt, x ≠ y ∧
      ∀ (p : Profile Individual Alt),
        (p j x y ∧ ¬ p j y x → f p x y ∧ ¬ f p y x) ∧
        (p j y x ∧ ¬ p j x y → f p y x ∧ ¬ f p x y))

-- Helper: a cycle in social preference contradicts choice function existence
private lemma cycle_contradicts_sdf {Alt : Type*} (R : PreferenceRelation Alt)
    (S : Finset Alt) (hS : S.Nonempty) (hcf : GeneratesChoiceFunction R)
    (hcycle : ∀ a ∈ S, ∃ b ∈ S, ¬ R a b) : False := by
  obtain ⟨x, hx, hbest⟩ := hcf S hS
  obtain ⟨b, hb, hn⟩ := hcycle x hx
  exact hn (hbest b hb)

/-
Case: two decisive pairs share one element, giving 3 distinct alternatives
i₁ decisive over (u, v), i₂ decisive over (v, w), Pareto completes cycle w > u
-/
private lemma sen_shared_element_case {Individual Alt : Type*} [DecidableEq Alt]
    (f : CCR Individual Alt) (hSDF : SDF f) (hP : ConditionP f)
    (i₁ i₂ : Individual) (hi : i₁ ≠ i₂)
    (u v w : Alt) (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w)
    (hD1 : ∀ p : Profile Individual Alt,
      p i₁ u v ∧ ¬ p i₁ v u → f p u v ∧ ¬ f p v u)
    (hD2 : ∀ p : Profile Individual Alt,
      p i₂ v w ∧ ¬ p i₂ w v → f p v w ∧ ¬ f p w v) :
    False := by
  -- Construct profile p where: i₁ prefers u > v, i₂ prefers v > w, and everyone prefers w > u.
  set p : Profile Individual Alt := fun k a b => (a = w ∧ b = u) ∨ (k = i₁ ∧ a = u ∧ b = v) ∨ (k = i₂ ∧ a = v ∧ b = w);
  -- By Pareto, $f p w u ∧ ¬ f p u w$.
  have hP_wu : f p w u ∧ ¬ f p u w := by
    exact hP p w u fun k => by aesop;
  -- By decisiveness, $f p u v ∧ ¬ f p v u$.
  have hD1_uv : f p u v ∧ ¬ f p v u := by
    grind;
  -- By decisiveness, $f p v w ∧ ¬ f p w v$.
  have hD2_vw : f p v w ∧ ¬ f p w v := by
    grind;
  have h_contradiction : ∀ (S : Finset Alt), S.Nonempty → ∃ x ∈ S, ∀ y ∈ S, f p x y := by
    exact hSDF p;
  specialize h_contradiction { u, v, w } ; simp_all +decide

/-
Case: decisive pairs are disjoint, giving 4 distinct alternatives
i₁ decisive over (x, y), i₂ decisive over (z, w), Pareto on y > z and w > x
-/
private lemma sen_disjoint_case {Individual Alt : Type*} [DecidableEq Alt]
    (f : CCR Individual Alt) (hSDF : SDF f) (hP : ConditionP f)
    (i₁ i₂ : Individual) (hi : i₁ ≠ i₂)
    (x y z w : Alt)
    (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w) (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w)
    (hD1 : ∀ p : Profile Individual Alt,
      p i₁ x y ∧ ¬ p i₁ y x → f p x y ∧ ¬ f p y x)
    (hD2 : ∀ p : Profile Individual Alt,
      p i₂ z w ∧ ¬ p i₂ w z → f p z w ∧ ¬ f p w z) :
    False := by
  -- Define: p k a b := (a = y ∧ b = z) ∨ (a = w ∧ b = x) ∨ (k = i₁ ∧ a = x ∧ b = y) ∨ (k = i₂ ∧ a = z ∧ b = w).
  set p : Profile Individual Alt := fun k a b => (a = y ∧ b = z) ∨ (a = w ∧ b = x) ∨ (k = i₁ ∧ a = x ∧ b = y) ∨ (k = i₂ ∧ a = z ∧ b = w);
  have h_cycle : f p x y ∧ ¬ f p y x ∧ f p y z ∧ ¬ f p z y ∧ f p z w ∧ ¬ f p w z ∧ f p w x ∧ ¬ f p x w := by
    have h1 : f p x y ∧ ¬ f p y x := by
      grind
    have h2 : f p y z ∧ ¬ f p z y := by
      exact hP p y z fun k => ⟨ by aesop, by aesop ⟩
    have h3 : f p z w ∧ ¬ f p w z := by
      grind +ring
    have h4 : f p w x ∧ ¬ f p x w := by
      convert hP p w x _ using 1;
      grind
    exact ⟨h1.left, h1.right, h2.left, h2.right, h3.left, h3.right, h4.left, h4.right⟩;
  convert cycle_contradicts_sdf ( f p ) { x, y, z, w } ?_ ( hSDF p ) ?_;
  · simp +decide;
  · grind

-- §14: Theorem II - The Impossibility of a Paretian Liberal
-- Following Sen (1970), the proof considers two cases for the decisive pairs (x,y) and (z,w):
--   Case 1: x = z (the pairs share an element)
--   Case 2: All four elements x, y, z, w are distinct
-- When another element is shared (x = w, y = z, or y = w), the symmetric
-- decisiveness conditions allow reducing to the x = z pattern.
theorem SenImpossibility {Individual : Type*} {Alt : Type*} [DecidableEq Alt]
    (f : CCR Individual Alt)
    (hSDF : SDF f)
    (_hU : ConditionU f)
    (hP : ConditionP f)
    (hL : ConditionL' f) : False := by
  obtain ⟨i, j, hij, ⟨x, y, hxy, hDi⟩, ⟨z, w, hzw, hDj⟩⟩ := hL
  -- Case 1: x = z (the decisive pairs share an element)
  by_cases hxz : x = z
  · by_cases hyw : y = w
    · -- x = z and y = w, so {x,y} = {z,w}. The two individuals are decisive
      -- over the same pair in opposite directions, giving a direct contradiction.
      let p : Profile Individual Alt := fun k a b =>
        (k = i ∧ a = x ∧ b = y) ∨ (k = j ∧ a = y ∧ b = x)
      have hpi : p i x y ∧ ¬ p i y x :=
        ⟨Or.inl ⟨rfl, rfl, rfl⟩, fun h => by
          rcases h with ⟨_, h1, _⟩ | ⟨h1, _, _⟩
          · exact hxy h1.symm
          · exact hij h1⟩
      have hpj : p j y x ∧ ¬ p j x y :=
        ⟨Or.inr ⟨rfl, rfl, rfl⟩, fun h => by
          rcases h with ⟨h1, _, _⟩ | ⟨_, h1, _⟩
          · exact hij h1.symm
          · exact hxy h1⟩
      have hfxy := ((hDi p).1 hpi).1
      have h := (hDj p).2; rw [← hxz, ← hyw] at h; exact (h hpj).2 hfxy
    · -- x = z, y ≠ w: three distinct elements y, x, w form a cycle
      -- y →(i, 2nd dir) x →(j, 1st dir) w →(Pareto) y
      exact sen_shared_element_case f hSDF hP i j hij y x w
        (Ne.symm hxy) (hxz.symm ▸ hzw) hyw
        (fun p => (hDi p).2) (fun p => hxz.symm ▸ (hDj p).1)
  -- Case 2: All four elements are distinct
  · -- When x ≠ z, if another element is shared we reduce to a shared-element
    -- cycle (analogous to Case 1) using the symmetric decisiveness conditions.
    -- Otherwise all four are distinct and we construct a 4-cycle.
    by_cases hyz : y = z
    · -- y = z, x ≠ z: if also x = w then {x,y} = {z,w} (same pair), otherwise shared element
      by_cases hxw : x = w
      · -- x = w, y = z: same pair {x,y} = {w,z}, direct contradiction
        let p : Profile Individual Alt := fun k a b =>
          (k = i ∧ a = x ∧ b = y) ∨ (k = j ∧ a = y ∧ b = x)
        have hpi : p i x y ∧ ¬ p i y x :=
          ⟨Or.inl ⟨rfl, rfl, rfl⟩, fun h => by
            rcases h with ⟨_, h1, _⟩ | ⟨h1, _, _⟩
            · exact hxy h1.symm
            · exact hij h1⟩
        have hpj : p j y x ∧ ¬ p j x y :=
          ⟨Or.inr ⟨rfl, rfl, rfl⟩, fun h => by
            rcases h with ⟨h1, _, _⟩ | ⟨_, h1, _⟩
            · exact hij h1.symm
            · exact hxy h1⟩
        have hfxy := ((hDi p).1 hpi).1
        have h := (hDj p).1; rw [← hyz, ← hxw] at h; exact (h hpj).2 hfxy
      · -- x ≠ w, y = z: cycle x →(i) y →(j) w →(Pareto) x
        exact sen_shared_element_case f hSDF hP i j hij x y w hxy
          (hyz.symm ▸ hzw) hxw
          (fun p => (hDi p).1) (fun p => hyz.symm ▸ (hDj p).1)
    · by_cases hxw : x = w
      · -- x = w: cycle z →(j) x →(i) y →(Pareto) z
        exact sen_shared_element_case f hSDF hP j i (Ne.symm hij) z x y
          (fun h => hzw (h.trans hxw)) hxy (fun h => hyz h.symm)
          (fun p => hxw.symm ▸ (hDj p).1) (fun p => (hDi p).1)
      · by_cases hyw : y = w
        · -- y = w: cycle x →(i) y →(j 2nd) z →(Pareto) x
          exact sen_shared_element_case f hSDF hP i j hij x y z hxy hyz hxz
            (fun p => (hDi p).1) (fun p => hyw.symm ▸ (hDj p).2)
        · -- All four elements x, y, z, w are distinct
          exact sen_disjoint_case f hSDF hP i j hij x y z w hxy hxz hxw hyz hyw hzw
            (fun p => (hDi p).1) (fun p => (hDj p).1)
