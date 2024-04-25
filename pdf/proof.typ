#import "@preview/ctheorems:1.1.2": *
#show: thmrules.with(qed-symbol: $square$)

#set heading(numbering: "1.1.")

#let theorem = thmbox("theorem", "Theorem", fill: rgb("#eeffee"))
#let corollary = thmplain(
  "corollary",
  "Corollary",
  base: "theorem",
  titlefmt: strong
)
#let definition = thmbox("definition", "Definition", inset: (x: 1.2em, top: 1em))

#let example = thmplain("example", "Example").with(numbering: none)
#let proof = thmproof("proof", "Proof")


= Hard direction

Let $g : V -> RR$ be an eigenvector achieving $lambda_G$.
- Let $s : {1,...,n} -> V$ be a function such that $g compose s$ is monotonically decreasing. Write $v_i$ for $s(i)$ and $g(i)$ for $g(s(i))$.
- Let $S_i = {v_1,...,v_i}$.
- Define $alpha_G = min_i h_S_i$.
- Let $r$ denote the largest integer such that $"vol"(S_r) < "vol"(G) / 2$, or in other words $op("vol")(S_r) < op("vol")(S_r^c)$.
- Define $f(v) := g(v) - g(v_r)$. Denote the positive and negative part of $f$ with $f_+$ and $f_-$ respectively.

#theorem[
  $i < j => f_+(i)^2 >= f_+(j)^2$
]
#proof[
  The only possible troublesome case is $f_+(i) = 0$ and $f_+(j) = f(j)$. In this case we have $g(i) < g(r) => i > r$ and $g(j) >= g(r) => j <= r$, a contradiction.
]

#theorem[
  $R(g_+) <= lambda_G$ or $R(g_-) <= lambda_G$
]
#proof[
  $
    lambda_G
    &= (sum_(u tilde v) (g(u) - g(v))^2) / (sum_v g(v)^2 d_v) \
    &>= (sum_(u tilde v) (g(u) - g(v_r) + g(v_r) - g(v))^2) / (sum_v (g(v) - g(v_r))^2 d_v) \
    &= (sum_(u tilde v) (f(u) - f(v))^2) / (sum_v f(v)^2 d_v) \
    &>= (sum_(u tilde v) (f_+(u) - f_+(v))^2 + (f_-(u) - f_-(v))^2) / (sum_v (f_+(v) - f_-(v))^2 d_v) \
    &>= (sum_(u tilde v) (f_+(u) - f_+(v))^2 + sum_(u tilde v) (f_-(u) - f_-(v))^2) / (sum_v f_+(v)^2 d_v + sum_v f_-(v)^2 d_v).
  $
  We close using the fact that
  $
    (a + b) / (c + d) >= min{a/c, b/d}. \
  $
]

#theorem[
  $
    sum_v g(v)^2 d_v <= sum_v (g(v) - g(v_r))^2 d_v
  $
]
#proof[
  $
    sum_v g(v)^2 d_v
    &= min_c sum_v (g(v)^2 + c^2) d_v - 2c underbrace(sum_v g(v) d_v, 0) \
    &= min_c sum_v (g(v) - c)^2 d_v \
    &<= sum_v (g(v) - g(v_r))^2 d_v
  $
]

#theorem[
  $ (f_+(x) - f_+(y))^2 + (f_-(x) - f_-(y))^2  <= (f(x) - f(y))^2 $
]
#proof[
  Done.
]

#theorem[
  $alpha_G^2 / 2 <= R(g_+)$
]
#proof[
  $
    alpha_G^2 / 2
    &= alpha_G^2 / 2 (sum_(i=1)^n f_+(i)^2 d_(i))^2 / (sum_(i=1)^n f_+(i)^2 d_(i))^2 \
    &<= alpha_G^2 / 2 (sum_(i=1)^n f_+(i)^2 (op("vol")(S_i) - op("vol")(S_(i-1))))^2 / (sum_(i=1)^n f_+(i)^2 d_(i))^2 \
    &= alpha_G^2 / 2 (sum_(i=1)^(n-1) (f_+(i)^2 - f_+(i+1)^2) op("vol")(S_i))^2 / (sum_(i=1)^n f_+(i)^2 d_(i))^2 & #text[@sum_by_parts] \
    &= alpha_G^2 / 2 (sum_(i=1)^(n-1) (f_+(i)^2 - f_+(i+1)^2) min{op("vol")S_i, op("vol")S_i^c})^2 / (sum_(i=1)^n f_+(i)^2 d_(i))^2 & "since" op("vol")S_i^c <= op("vol")S_i => f_+(i) = 0. \
    &<= (sum_(i=1)^(n-1) (f_+(i)^2 - f_+(i+1)^2) abs(partial(S_i)))^2 / (2(sum_(i=1)^n f_+(i)^2 d_(i))^2) & #text[@alpha_mul_vol_le_cut] \
    &<= (sum_(i tilde j) f_+(i)^2 - f_+(j)^2)^2 / (2sum_(i=1)^n f_+(i)^2 d_(i))^2 & #text[@by_counting] \
    &<= ((sum_(i tilde j) (f_+(i) + f_+(j))^2)(sum_(i tilde j) (f_+(i) - f_+(j))^2)) / (sum_(i=1)^n f_+(i)^2 d_(i))^2 & #text[@cauchy_schwarz] \
    &<= ((sum_(i tilde j) (f_+(i) + f_+(j))^2)(sum_(i tilde j) (f_+(i) - f_+(j))^2)) / ((sum_(i=1)^n f_+(i)^2 d_(i))(sum_(i tilde j) (f_+(i) + f_+(j))^2)) & #text[@sum_f2_mul_deg] \
    &= (sum_(i tilde j) (f_+(i) - f_+(j))^2) / (sum_(i=1)^n f_+(i)^2 d_(i)) \
    &= (sum_(u tilde v) (g_+(u) - g_+(v))^2) / (sum_(v) g_+(v)^2 d_(v)) \
    &= R(g_+).
  $
]

/*
#theorem[
  $
    d_i <= abs(min{"vol"(S_(i)), "vol"(S_(i)^c)} - min{"vol"(S_(i-1)), "vol"(S_(i-1)^c)})
  $
]<degree_le>
#proof[
  - Case $"vol"(S_i) <= "vol"(S_i^c)$ and $"vol"(S_(i-1)) <= "vol"(S_(i-1)^c)$: TODO
  - Case $"vol"(S_i) >= "vol"(S_i^c)$ and $"vol"(S_(i-1)) >= "vol"(S_(i-1)^c)$: TODO
  - Case $"vol"(S_i) <= "vol"(S_i^c)$ and $"vol"(S_(i-1)) >= "vol"(S_(i-1)^c)$: This is a contradiction, \ indeed $(S_i) <= (S_i^c) <= (S_(i-1)^c) <= (S_(i-1))$
  - Case $"vol"(S_i) >= "vol"(S_i^c)$ and $"vol"(S_(i-1)) <= "vol"(S_(i-1)^c)$: In this case we have $(S_(i-1)) <= (G)/2$ and therefore $(G) - 2 dot (S_(i-1)) - d_i >= (G) - 2 dot (G)/2 - d_i$.
  $
    op("vol")(S_i^c) - op("vol")(S_(i-1))
    &= op("vol")(G) - op("vol")(S_i) - op("vol")(S_(i-1)) \
    &= op("vol")(G) - op("vol")(S_(i-1)) - d_i - op("vol")(S_(i-1)) \
    &= op("vol")(G) - 2 op("vol")(S_(i-1)) - d_i \
    &>= op("vol")(G) - 2 (op("vol")(G))/2 - d_i \
    &= -d_i.
  $
  wrong
]
*/

#theorem[
  $ sum_(i=1)^n f_+(i)^2 (op("vol")(S_i) - op("vol")(S_(i-1))) = sum_(i=1)^(n-1) (f_+(i)^2 - f_+(i+1)^2) op("vol")(S_i)$.
]<sum_by_parts>
#proof[
  $
    sum_(i=1)^n f_+(i)^2 (op("vol")(S_i) - op("vol")(S_(i-1)))
    = sum_(i=1)^n f_+(i)^2 op("vol")(S_i) - sum_(i=1)^n f_+(i)^2 op("vol")(S_(i-1)) \
    = sum_(i=1)^(n-1) f_+(i)^2 op("vol")(S_i) + cancel(f_+(n)^2 op("vol")(S_n)) - sum_(i=1)^(n-1) f_+(i+1)^2 op("vol")(S_(i)) - cancel(f_+(1)^2 op("vol")(S_0)) \
    = sum_(i=1)^(n-1) (f_+(i)^2 - f_+(i+1)^2) op("vol")(S_i).
  $
]

#theorem[
  $ alpha_G min{"vol"(S_(i)), "vol"(S_(i)^c)} <= abs(partial(S_i)) $
]<alpha_mul_vol_le_cut>
#proof[
  $
    min_j abs(partial(S_j)) / min{"vol"(S_(j)), "vol"(S_(j)^c)} dot min{"vol"(S_(i)), "vol"(S_(i)^c)} \
    <= abs(partial(S_i)) / min{"vol"(S_(i)), "vol"(S_(i)^c)} dot min{"vol"(S_(i)), "vol"(S_(i)^c)}
    = abs(partial(S_i)).

  $
]

#theorem[
  $
    sum_(i=1)^n (f_+(i)^2 - f_+(i+1)^2)partial(S_i)
    <=
    sum_(i tilde j) f_+(i)^2 - f_+(j)^2
  $
]<by_counting>
#proof[
  $
    sum_(i=1)^(n) (f_+(i)^2 - f_+(i+1)^2)partial(S_i)
    &= sum_(i=1)^(n) (f_+(i)^2 - f_+(i+1)^2)(sum_(j=(i+1))^n 1_(i tilde j)) \
    &= sum_(i=1)^(n-1)sum_(j=(i+1))^n (f_+(i)^2 - f_+(i+1)^2)1_(i tilde j) \
    &<= sum_(i=1)^(n-1)sum_(j=(i+1))^n (f_+(i)^2 - f_+(j)^2)1_(i tilde j) & j > i => f_+(i)^2 - f_+(j)^2 >= 0 \
    &= sum_(i tilde j)(f_+(i)^2 - f_+(j)^2).
  $
]

#theorem[
  $ (sum_(i tilde j) f_+(i)^2 - f_+(j)^2)^2 <= 2 (sum_(i tilde j) (f_+(i) + f_+(j))^2)(sum_(i tilde j) (f_+(i) - f_+(j))^2) $
]<cauchy_schwarz>
#proof[
  Consider the matrices $X(i, j) = 1_(i tilde j)(f_+(i) + f_+(j))$ and $Y(i, j) = 1_(i tilde j, i<j)(f_+(i) - f+(j))$. Their Frobenius inner product is
  $
    angle.l X, Y angle.r
    = sum_(i, j) X^T (i,j) Y(i, j) \
    = sum_(i, j) 1_(i tilde j, i<j)(f_+(i) + f_+(v))(f_+(i) - f_+(j)) \
    = sum_(i tilde j) f_+(i)^2 - f_+(j)^2.
  $
  The norms of $X$ and $Y$ are
  $
    norm(X)_F^2 = sum_(i, j) X(i, j)^2 = sum_(i, j) 1_(i tilde j) (f_+(i) + f_+(j))^2 = 2 sum_(i tilde j) (f_+(i) + f_+(j))^2, \
    norm(Y)_F^2 = sum_(i, j) Y(i, j)^2 = sum_(i, j) 1_(i tilde j, i<j) (f_+(i) - f_+(j))^2 = sum_(i tilde j) (f_+(i) - f_+(j))^2.
  $
  By the Cauchy-Schwarz inequality we have
  $
   angle.l X, Y angle.r^2 <= norm(X)_F^2 norm(Y)_F^2,
  $
  and the theorem follows.
]

#theorem[
  $
    sum_(i tilde j) (f_+(i) + f_+(j))^2 <= sum_i f_+(i)^2d_i
  $
]<sum_f2_mul_deg>
#proof[
  $
    sum_(i tilde j) (g_+(i) + g_+(j))^2 \
    <= sum_(i tilde j) g_+(i)^2 + g_+(j)^2 \
    = sum_(i tilde j) g_+(i)^2 + sum_(i tilde j) g_+(j)^2 \
    = 2 sum_(i tilde j) g_+(i)^2 \
    = 2 dot 1/2 sum_i g_+(i)^2 sum_j 1_(i tilde j) \
    = sum_i g_+(i)^2 d_i.
  $
]
