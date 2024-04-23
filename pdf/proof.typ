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

Let $g : V -> RR$ be an eigenvector achieving $lambda_G$. Let $s : {1,...,n} -> V$ be a function such that $f := g compose s$ is monotonically decreasing. Let $S_i = {s(1),...,s(i)}$. Define $alpha_G = min_i h_S_i$. Let $r$ denote the largest integer such that $"vol"(S_r) <= "vol"(G) / 2$.

#theorem[
  $alpha_G^2 / 2 <= R(g_+)$
]
#proof[
  $
    alpha_G^2 / 2
    &= alpha_G^2 / 2 (sum_(i=1)^n f_+(i)^2 d_(s(i)))^2 / (sum_(i=1)^n f_+(i)^2 d_(s(i)))^2 \
    &<= alpha_G^2 / 2 (sum_(i=1)^n f_+(i)^2 abs(tilde("vol")(S_i) - tilde("vol")(S_(i-1))))^2 / (sum_(i=1)^n f_+(i)^2 d_(s(i)))^2 & #text[@degree_le] \
    &= alpha_G^2 / 2 (sum_(i=1)^(n-1) (f_+(i)^2 - f_+(i+1)^2) tilde("vol")(S_i))^2 / (sum_(i=1)^n f_+(i)^2 d_(s(i)))^2 & #text[@sum_by_parts] \
    &<= (sum_(i=1)^(n-1) (f_+(i)^2 - f_+(i+1)^2) abs(partial(S_i)))^2 / (2(sum_(i=1)^n f_+(i)^2 d_(s(i)))^2) & #text[@alpha_mul_vol_le_cut] \
    &<= (sum_(s(i) tilde s(j)) f_+(i)^2 - f_+(j)^2)^2 / (2sum_(i=1)^n f_+(i)^2 d_(s(i)))^2 \
    &<= ((sum_(s(i) tilde s(j)) (f_+(i) + f_+(j))^2)(sum_(s(i) tilde s(j)) (f_+(i) - f_+(j))^2)) / (sum_(i=1)^n f_+(i)^2 d_(s(i)))^2 \
    &<= ((sum_(s(i) tilde s(j)) (f_+(i) + f_+(j))^2)(sum_(s(i) tilde s(j)) (f_+(i) - f_+(j))^2)) / ((sum_(i=1)^n f_+(i)^2 d_(s(i)))(sum_(s(i) tilde s(j)) (f_+(i) + f_+(j))^2)) \
    &= (sum_(s(i) tilde s(j)) (f_+(i) - f_+(j))^2) / (sum_(i=1)^n f_+(i)^2 d_(s(i))) \
    &= (sum_(u tilde v) (g_+(u) - g_+(v))^2) / (sum_(v) g_+(v)^2 d_(v)) \
    &= R(g_+).
  $
]

#theorem[
  $
    d_s(i) <= abs(min{"vol"(S_(i)), "vol"(S_(i)^c)} - min{"vol"(S_(i-1)), "vol"(S_(i-1)^c)})
  $
]<degree_le>
#proof[
  - Case $"vol"(S_i) <= "vol"(S_i^c)$ and $"vol"(S_(i-1)) <= "vol"(S_(i-1)^c)$: TODO
  - Case $"vol"(S_i) >= "vol"(S_i^c)$ and $"vol"(S_(i-1)) >= "vol"(S_(i-1)^c)$: TODO
  - Case $"vol"(S_i) <= "vol"(S_i^c)$ and $"vol"(S_(i-1)) >= "vol"(S_(i-1)^c)$: This is a contradiction, \ indeed $(S_i) <= (S_i^c) <= (S_(i-1)^c) <= (S_(i-1))$
  - Case $"vol"(S_i) >= "vol"(S_i^c)$ and $"vol"(S_(i-1)) <= "vol"(S_(i-1)^c)$: In this case we have $(S_(i-1)) <= (G)/2$ and therefore $(G) - 2 dot (S_(i-1)) - d_i >= (G) - 2 dot (G)/2 - d_i$
]

#theorem[
  $ sum_(i=1)^n f_+(i)^2 abs(tilde("vol")(S_i) - tilde("vol")(S_(i-1))) = sum_(i=1)^(n-1) (f_+(i)^2 - f_+(i+1)^2) tilde("vol")(S_i)$.
]<sum_by_parts>
#proof[
  $
    sum_(i=1)^n f_+(i)^2 abs(tilde("vol")(S_i) - tilde("vol")(S_(i-1)))
    = abs(sum_(i=1)^n f_+(i)^2 tilde("vol")(S_i) - sum_(i=1)^n f_+(i)^2 tilde("vol")(S_(i-1))) \
    = abs(sum_(i=1)^(n-1) f_+(i)^2 tilde("vol")(S_i) + cancel(f_+(n)^2tilde("vol")(S_n)) - sum_(i=1)^(n-1) f_+(i+1)^2 tilde("vol")(S_(i)) - cancel(f_+(1)^2 tilde("vol")(S_0))) \
    = abs(sum_(i=1)^(n-1) (f_+(i)^2 - f_+(i+1)^2) tilde("vol")(S_i)).
  $
  The theorem follows from the fact that every summand is positive.
]

#theorem[
  $ alpha_G op(tilde("vol"))(S_i) <= abs(partial(S_i)) $
]<alpha_mul_vol_le_cut>
#proof[
  $
    min_j abs(partial(S_j)) / min{"vol"(S_(j)), "vol"(S_(j)^c)} dot min{"vol"(S_(i)), "vol"(S_(i)^c)} \
    <= abs(partial(S_i)) / min{"vol"(S_(i)), "vol"(S_(i)^c)} dot min{"vol"(S_(i)), "vol"(S_(i)^c)}
    = abs(partial(S_i)).

  $
]

#theorem[
  $g_+(v_i)^2 >= g_+(v_(i+1))^2$
]
#proof[
  The only troublesome cases is when $g_+(v_i) = 0$ and $g_+(v_(i+1)) = g(v_(i+1))$. In this case we have $g(v_i) < g(v_r)$ and $g(v_(i+1)) >= g(v_r)$ which implies $r < i$ and $i+1 <=r$. This is a contradiction.
]

#theorem[
  $ (sum_(u tilde v) g_+(u)^2 - g_+(v)^2)^2 <= 2 (sum_(u tilde v) (g_+(u) + g_+(v))^2)(sum_(u tilde v) (g_+(u) - g_+(v))^2) $
]
#proof[
  Consider the matrices $X(i, j) = 1_(s(i) tilde s(j))(f_+(i) + f_+(j))$ and $Y(i, j) = 1_(s(i) tilde s(j), i<j)(f_+(i) - f+(j))$. Their Frobenius inner product is
  $
    angle.l X, Y angle.r
    = sum_(i, j) X^T (i,j) Y(i, j) \
    = sum_(i, j) 1_(s(i) tilde s(j), i<j)(f_+(i) + f_+(v))(f_+(i) - f_+(j)) \
    = sum_(s(i) tilde s(j)) f_+(i)^2 - f_+(j)^2.
  $
  The norms of $X$ and $Y$ are
  $
    norm(X)_F^2 = sum_(u, v) X(u, v)^2 = sum_(u, v) 1_(u tilde v) (g_+(u) + g_+(v))^2 = 2 sum_(u tilde v) (g_+(u) + g_+(v))^2, \
    norm(Y)_F^2 = sum_(u, v) Y(u, v)^2 = sum_(u, v) 1_(u tilde v, u<v) (g_+(u) - g_+(v))^2 = sum_(u tilde v) (g_+(u) - g_+(v))^2.
  $
  By the Cauchy-Schwarz inequality we have
  $
   angle.l X, Y angle.r^2 <= norm(X)_F^2 norm(Y)_F^2,
  $
  and the theorem follows.
]

#theorem[
  $
    sum_(u tilde v) (g_+(u) + g_+(v))^2 <= sum_u g_+(u)^2d_u
  $
]
#proof[
  $
    sum_(u tilde v) (g_+(u) + g_+(v))^2 \
    <= sum_(u tilde v) g_+(u)^2 + g_+(v)^2 \
    = sum_(u tilde v) g_+(u)^2 + sum_(u tilde v) g_+(v)^2 \
    = 2 sum_(u tilde v) g_+(u)^2 \
    = 2 dot 1/2 sum_u g_+(u)^2 sum_v 1_(u tilde v) \
    = sum_u g_+(u)^2 d_u.
  $
]

#theorem[
  $
    sum_(i=1)^n (f_+(i)^2 - f_+(i+1)^2)partial(S_i)
    <=
    sum_(u tilde v) g_+(u)^2 - g_+(v)^2
  $
]
#proof[
  $
    sum_(i=1)^(n) (f_+(i)^2 - f_+(i+1)^2)partial(S_i)
    = sum_(i=1)^(n) (f_+(i)^2 - f_+(i+1)^2)(sum_(j=(i+1))^n 1_(s(i) tilde s(j))) \
    = sum_(i=1)^(n-1)sum_(j=(i+1))^n (f_+(i)^2 - f_+(i+1)^2)1_(s(i) tilde s(j)).
  $
  By monotonicity we have $f_+(i)^2 - f_+(i+1)^2 >= 0$ for $i < j$. Therefore the above is less or equal
  $
    sum_(i=1)^(n-1)sum_(j=(i+1))^n (f_+(i)^2 - f_+(j)^2)1_(s(i) tilde s(j))
    = sum_(s(i) tilde s(j))(f_+(i)^2 - f_+(j)^2).
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
  $R(g_+) <= lambda_G$ or $R(g_-) <= lambda_G$
]
#proof[
  $
    lambda_G
    &= (sum_(u tilde v) (g(u) - g(v))^2) / (sum_v g(v)^2 d_v) \
    &>= (sum_(u tilde v) (g(u) - g(v))^2) / (sum_v g(v)^2 d_v) \
  $

  - Case $g(v_r) <= g(u)$ and $g(u) <= g(v_r)$ \
    $g_+(u) - g_+(v) = g(u) - g(v_r)$ and $g_-(u) - g_-(v) = 0$ \
    $(g_+(u) - g_+(v))^2 + (g_+(u) - g_+(v)) = (g(v) - g(v))^2$
  - Case $g(v_r) > g(u)$ and $g(u) > g(v_r)$ \
    $g_+(u) - g_+(v) = g(v) - g(v)$ and $g_-(u) - g_-(v) = 0$ \
    $(g_+(u) - g_+(v))^2 + (g_+(u) - g_+(v)) = (g(v) - g(v))^2$
  - Case $g(v_r) > g(u)$ and $g(u) <= g(v_r)$ \
    TODO
  - Case $g(v_r) <= g(u)$ and $g(u) > g(v_r)$ \
    TODO
]
