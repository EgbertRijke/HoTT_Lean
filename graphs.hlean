open sigma eq

namespace graphs
-- We will define all the ingredients of the graph model of type theory

-- The context in the graph model are the graphs themselves
structure ctx :=
  ( vertex : Type)
  ( edge : vertex → vertex → Type)

-- The families in the graph model are families of graphs
structure fam (G : ctx)
  :=
  ( vertex : ctx.vertex G → Type)
  ( edge : Π{i j : ctx.vertex G}, ctx.edge G i j → vertex i → vertex j → Type)

-- Global terms of families are matching families of terms
structure tm {G : ctx} (A : fam G) :=
  ( vertex : Π(i : ctx.vertex G), fam.vertex A i)
  ( edge : Π{i j : ctx.vertex G}, Π(e : ctx.edge G i j), fam.edge A e (vertex i) (vertex j))

section graph_in_context

variable {G : ctx}

-- Extension in the graph model is interpetred using Sigma (by lack of something better)
definition ctxext (A : fam G) : ctx :=
  ctx.mk
    ( Σ (i : ctx.vertex G), fam.vertex A i)
    ( λ p q,
        Σ (e : ctx.edge G (pr1 p) (pr1 q)),
          fam.edge A e (pr2 p) (pr2 q))

-- There is also family extension, which turns out to be equivalent to the dependent
-- pair graph
definition famext (A : fam G) (P : fam (ctxext A)) : fam G :=
  fam.mk
    ( λ i, Σ (x : fam.vertex A i), fam.vertex P ⟨i,x⟩)
    ( λ i j e p q,
        Σ (f : fam.edge A e (pr1 p) (pr1 q)),
          fam.edge P ⟨e,f⟩ (pr2 p) (pr2 q))

-- Types as graphs.
definition Delta (A : Type) : ctx :=
  ctx.mk A (λ x y, x = y)

-- Weakening
section wk

variable A : fam G

definition wk.ctx (B : fam G) : fam (ctxext A) :=
  fam.mk
    ( λ p, fam.vertex B (pr1 p))
    ( λ p q e, fam.edge B (pr1 e))

end wk

end graph_in_context

end graphs
