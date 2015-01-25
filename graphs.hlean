open sigma

namespace graphs

structure ctx :=
  (vertex : Type)
  (edge : vertex → vertex → Type)

structure fam (G : ctx) :=
  (vertex : ctx.vertex G → Type)
  (edge : Π{i j : ctx.vertex G}, ctx.edge G i j → vertex i → vertex j → Type)

structure tm {G : ctx} (A : fam G) :=
  (vertex : Π(i : ctx.vertex G), fam.vertex A i)
  (edge : Π{i j : ctx.vertex G}, Π(e : ctx.edge G i j), fam.edge A e (vertex i) (vertex j))

section graph_in_context

variable G : ctx

definition extension (A : fam G) : ctx :=
  ctx.mk
    ( Σ (i : ctx.vertex G), (fam.vertex A i))
    ( λ (p q : Σ(i : ctx.vertex G), (fam.vertex A i)),
        Σ (e : ctx.edge G (pr1 p) (pr1 q)),
          fam.edge A e (pr2 p) (pr2 q))

end graph_in_context

end graphs
