import topology.metric_space.basic

noncomputable theory 

open topological_space filter

universe u            -- the universe we work in
variable {X : Type u} -- the underlying set for our space

/-- input a pseudo_metric_space and a set. Returns a collection of open sets centered on that set. -/
def base_of_metric_and_set [M : pseudo_metric_space X] (D : set X) : 
set (set X) := { Y | ∃(n:ℕ) (d:X), d ∈ D ∧ metric.ball d (1/(↑n+1)) = Y }

/-This is a lemma to make it easier to access the inner sets.-/
lemma sets_in_base [M : pseudo_metric_space X] (D : set X) : ∀(n:ℕ) (d ∈ D), metric.ball d (1/(↑n+1)) ∈ base_of_metric_and_set D :=
begin
  intros n d hd,
  refine set.mem_def.mpr _,
  split,
  use d,
  split, 
  exact hd,
  simp,
end

/- This is a lemma to more easily say dense set intsersect all balls.-/
lemma dense_set_int_balls [M : pseudo_metric_space X] (D : set X) (hD : dense D) (x:X) (r:ℝ) ( hr_pos : r>0): set.nonempty ((metric.ball x r) ∩ D) :=
begin
  have ball_open := @metric.is_open_ball X M x r, 
  have ball_nonempty := @metric.nonempty_ball X M x r,
  rcases ball_nonempty with ⟨-,ball_nonempty⟩,
  specialize ball_nonempty hr_pos,
  have D_int_ball := dense.inter_open_nonempty hD (metric.ball x r) ball_open ball_nonempty, 
  exact D_int_ball,
end

lemma sets_in_nbhd [M : pseudo_metric_space X] (D : set X) (hD : dense D) (U : set X) ( hU : is_open U) (x : X) (hx : x ∈ U): 
∃(n:ℕ) (d ∈ D), metric.ball d (1/(↑n+1)) ⊆ U ∧ x ∈ metric.ball d (1/(n+1 : ℝ)) :=
begin
  have hdist := (@metric.is_open_iff X M U),
  rcases hdist with ⟨hdist , -⟩,
  replace hdist := hdist hU x hx,
  rcases hdist with ⟨δ, ⟨δ_pos, hball⟩ ⟩,
  have δ2_pos : δ/2 > 0 := by linarith,
  have hyp := exists_nat_one_div_lt (δ2_pos),
  cases hyp with n n_less_δ2,
  have int_nonempty := dense_set_int_balls D hD x (1 / (↑n + 1)) (nat.one_div_pos_of_nat),
  have d_in_int := @set.nonempty.some_mem X (metric.ball x (1 / (↑n + 1)) ∩ D) int_nonempty,
  cases d_in_int with d_in_ball_xn d_in_D,
  use [n, int_nonempty.some, d_in_D],
  set d := int_nonempty.some,
  split,
  have ball_dn_subset_ball_xδ : metric.ball d (1/(↑n + 1)) ⊆ metric.ball x δ,
  { have h_dist := @metric.mem_ball X M x d (1/(↑n + 1)),
    rcases h_dist with ⟨h_dist, -⟩,
    specialize h_dist d_in_ball_xn,
    refine metric.ball_subset _,    
    linarith  },
  exact set.subset.trans ball_dn_subset_ball_xδ hball,
  have final := @metric.mem_ball_comm X M x d (1 / (↑n+1)),
  rw final,
  exact d_in_ball_xn,
end

/--The construction results in a topological basis when the set is dense. -/
lemma metric_and_dense_is_basis [M : pseudo_metric_space X] (D : set X) (hD : dense D): topological_space.is_topological_basis (base_of_metric_and_set D) :=
begin
  set BASIS := base_of_metric_and_set D,
  have hopen : ∀B ∈ BASIS, is_open B, 
  { rintro B ⟨n, ⟨d, ⟨hd, b2⟩⟩⟩,
    rw ← b2,
    apply metric.is_open_ball },
  have hbase : ∀ x:X, ∀ U:set X, (x ∈ U)  → is_open U → (∃ (B : set X) (H : B ∈ BASIS), x ∈ B ∧ B ⊆ U),
  { intros x U U_is_nbhd U_is_open,
    have openiff := @metric.is_open_iff X M U,
    rcases openiff with ⟨case1,-⟩,
    replace case1 := case1 U_is_open,
    specialize case1 x U_is_nbhd,
    rcases case1 with ⟨ε,  ⟨ε_geq, Hball_subset⟩⟩, 
    have HBnbhd := sets_in_nbhd D hD U U_is_open x U_is_nbhd,
    rcases HBnbhd with ⟨Jn, ⟨Jd, ⟨JD, ⟨Jhu, Jhx⟩⟩⟩⟩,
    use metric.ball Jd (1 / (↑Jn+1)),
    split,
    apply sets_in_base D Jn Jd JD,
    split,
    apply Jhx,
    apply Jhu },
  exact is_topological_basis_of_open_of_nhds (hopen) (hbase),
end