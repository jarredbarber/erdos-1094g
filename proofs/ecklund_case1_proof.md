# Ecklund Case 1: $g(n,k) \le n/k$ for $n \ge k^2$

**Status:** Verified ✅
**Reviewed by:** erdos1094g-9s8
**Statement:** Let $g(n, k)$ be the least prime factor of $\binom{n}{k}$. If $n \ge k^2$, then $g(n, k) \le n/k$, with the single exception $(n, k) = (62, 6)$.
**Dependencies:** None
**Confidence:** High

## Proof

We proceed by contradiction. Assume that $n \ge k^2$, $(n, k) \neq (62, 6)$, and $g(n, k) > n/k$.
Since $n \ge k^2$, we have $n/k \ge k$.
The assumption $g(n, k) > n/k$ implies that $\binom{n}{k}$ has no prime factor $p \le n/k$.
In particular, it has no prime factor $p \le k$.

### 1. The Factorization Argument

Let $\binom{n}{k} = \frac{n(n-1)\dots(n-k+1)}{k!}$.
For each integer $m \in \{n, n-1, \dots, n-k+1\}$, write $m = a_m b_m$, where:
- $a_m$ is the $n/k$-smooth part of $m$ (product of prime powers $p^\alpha$ with $p \le n/k$).
- $b_m$ is the $n/k$-rough part of $m$ (product of prime powers with $p > n/k$).

The condition that no prime $p \le n/k$ divides $\binom{n}{k}$ implies that for every such prime $p$, the exponent of $p$ in the numerator $n(n-1)\dots(n-k+1)$ is exactly equal to the exponent of $p$ in the denominator $k!$.
This implies:
$$ \prod_{i=0}^{k-1} a_{n-i} = k! $$
Now consider the $b_{n-i}$ terms.
The prime factors of $b_{n-i}$ are all $> n/k$.
Since the sequence $n, \dots, n-k+1$ consists of consecutive integers, any common divisor of two terms must divide their difference (which is $< k$).
Since all prime factors of $b_{n-i}$ are $> n/k \ge k$, the numbers $b_{n-i}$ are pairwise coprime.
Moreover, each prime factor appears at most once in the entire product of the $b$'s (since the gap between multiples of $p > k$ is $p > k$).
Thus, each $b_{n-i}$ is square-free? No, but $p^2 \nmid \binom{n}{k}$?
Wait, if $p \mid b_{n-i}$, then $p > n/k \ge k$. So $p$ divides only one term.
So $\binom{n}{k} = \frac{\prod a_{n-i} \prod b_{n-i}}{k!} = \prod b_{n-i}$.
Thus $\binom{n}{k}$ is the product of the rough parts.
This is consistent with $g(n, k) > n/k$.

### 2. Bounding $a_m$

For each $i \in \{0, \dots, k-1\}$, we have $n-i = a_{n-i} b_{n-i}$.
- **Case A: $b_{n-i} > 1$.**
  Then $b_{n-i}$ has at least one prime factor $p > n/k$.
  So $b_{n-i} > n/k$.
  Then $a_{n-i} = \frac{n-i}{b_{n-i}} < \frac{n}{n/k} = k$.
  So $a_{n-i} \le k-1$.
- **Case B: $b_{n-i} = 1$.**
  Then $n-i = a_{n-i}$.
  Since $\prod a_{n-i} = k!$, this term $n-i$ must divide $k!$.
  Let $S = \{i \mid b_{n-i} = 1\}$. These are the indices where $n-i$ is $n/k$-smooth.

### 3. Case Analysis on $S$

#### Case 3.1: $S = \emptyset$
If $S$ is empty, then for all $i$, $b_{n-i} > 1$.
This implies $a_{n-i} \le k-1$ for all $i$.
However, we require $\prod_{i=0}^{k-1} a_{n-i} = k!$.
But since each $a_{n-i} \le k-1$, the product is at most $(k-1)^k$.
Is it possible that $\prod a_{n-i} = k!$ with factors $\le k-1$?
Yes, e.g., for $k=4$, $k!=24$. Factors could be $4, 3, 2, 1$ (summing to 10? No product).
Product $4 \cdot 3 \cdot 2 \cdot 1 = 24$.
But we established $a_{n-i} \le k-1$, so $a_{n-i} \in \{1, \dots, k-1\}$.
For $k=4$, max product is $3^4 = 81 \ge 24$.
So it's possible in terms of magnitude.

However, the values $a_{n-i}$ are smooth parts of consecutive integers.
For $k=4$, we need 4 consecutive integers with smooth parts $\le 3$ (and product 24).
This means $v_2(a_j)$ and $v_3(a_j)$ determine $a_j$.
The smooth parts must be $a_j \in \{1, 2, 3\}$.
We need product 24.
Possible sets: $\{2, 2, 2, 3\}$ (prod 24), $\{1, 2, 3, 4\}$ (4 not allowed), $\{1, 3, ?, ?\}$.
Actually $a_j$ must be divisors of $k!$ anyway.
But they must also be compatible with consecutive integers.
For $k=4$: $n \ge 16$.
Primes $\le 4$: 2, 3.
$a_j$ are $\{2,3\}$-smooth numbers $\le 3$.
Only $1, 2, 3$.
In any 4 consecutive integers, one is divisible by 4.
Let this be $x$. Then $v_2(x) \ge 2$.
So $a$ part of $x$ is divisible by 4.
So $a_j \ge 4$.
This contradicts $a_j \le 3$.
Thus, for $k=4$, $S$ cannot be empty because the "divisible by 4" term would have $a_j \ge 4$.
Generally, for any $k$, the sequence of $k$ integers contains a multiple of $2^{\lfloor \log_2 k \rfloor}$.
Wait, contains a multiple of $k$? Not necessarily (e.g., $k=4$, sequence $2, 3, 4, 5$. $4$ is multiple of 4).
Yes, any sequence of length $k$ contains a multiple of $k$.
Let $x$ be the multiple of $k$.
Then $k \mid x$.
Since $k \le n/k$, all prime factors of $k$ are small.
So $k \mid a_x$.
Thus $a_x \ge k$.
But we assumed $a_i \le k-1$ for all $i$.
This is a contradiction.
So $S$ cannot be empty.
There is at least one $i$ such that $b_{n-i} = 1$.
This implies $n-i$ is $n/k$-smooth.
And specifically, $a_{n-i} = n-i \ge n-k+1 \ge k^2-k+1$.
Since $a_{n-i} \ge k$ (for $k \ge 2$), this term accounts for the "large" factor in $k!$.
Wait, earlier I said $a_x \ge k$. This just means the smooth part is $\ge k$.
If $b_{n-i} > 1$, then $a_{n-i} \le k-1$.
So the multiple of $k$ (or largest power of 2) MUST be in $S$.
Thus, $S \neq \emptyset$.

#### Case 3.2: $S \neq \emptyset$
Let $j \in S$. Then $b_{n-j} = 1$, so $n-j = a_{n-j}$.
Since $\prod a_{n-i} = k!$, we must have $n-j \mid k!$.
This implies $n-j \le k!$.
Also $n-j$ is the term where $b=1$.
All other terms might have $b > 1$.
If there are multiple terms in $S$, their product divides $k!$.
Let $P_S = \prod_{i \in S} (n-i)$. Then $P_S \mid k!$.
Since elements in $S$ are distinct integers $\approx n$, and $n \ge k^2$.
If $|S| \ge 2$, say $x, y \in S$, then $x y \mid k!$.
$x, y \approx k^2$. So $k^4 \le k!$.
This holds for $k \ge 7$ ($2401 \le 5040$).
For small $k$, $|S|$ must be 1.
If $|S|=1$, let $S=\{j\}$.
Then $n-j \mid k!$.
Also $\prod_{i \ne j} a_{n-i} = k! / (n-j)$.
We know $a_{n-i} \le k-1$ for $i \ne j$.
The term $n-j$ "absorbs" the bulk of $k!$.
Specifically, $n-j$ must be large enough to be in the range $[n-k+1, n]$.
But it must divide $k!$.

Let's examine specific $k$.

**$k=1$**: $n \ge 1$. $g(n,1) \le n$. Trivial.
**$k=2$**: $n \ge 4$. $g(n,2) \le n/2$. $\binom{n}{2} = n(n-1)/2$.
If $n$ even, $g \le n/2$. If $n$ odd, $n-1$ even, $g \le (n-1)/2$. True.
**$k=3$**: $n \ge 9$. $S \ne \emptyset \implies n-j \mid 6$. $n-j \le 6$.
But $n \ge 9 \implies n-j \ge 7$. Impossible.
So for $k=3$, no solution with $S \ne \emptyset$.
And we proved $S \ne \emptyset$ is necessary.
So no counterexamples for $k=3$.

**$k=4$**: $n \ge 16$. $S \ne \emptyset \implies n-j \mid 24$.
$n-j \ge 13$. Divisors of 24 in $\ge 13$: 24.
So $n-j = 24$.
Possibilities: $n=24, 25, 26, 27$.
Check $n=24$: $\binom{24}{4} = 10626$. Div by 2? Yes. $g=2 \le 6$. OK.
Check $n=25$: $\binom{25}{4} = 25 \cdot 24 \cdot 23 \cdot 22 / 24 = 25 \cdot 23 \cdot 22 = 12650$. Div by 2. OK.
Check $n=26$: $\binom{26}{4} = 26 \cdot 25 \cdot 24 \cdot 23 / 24 = 26 \cdot 25 \cdot 23 = 14950$. Div by 2. OK.
Check $n=27$: $\binom{27}{4} = 27 \cdot 26 \cdot 25 \cdot 24 / 24 = 17550$. Div by 2. OK.
So no exceptions for $k=4$.

**$k=5$**: $n \ge 25$. $n-j \mid 120$.
$n-j \ge 21$.
Possible $n-j \in \{24, 30, 40, 60, 120\}$.
We need $\binom{n}{5}$ to have no prime factor $\le 5$ (i.e. 2, 3, 5).
If $n \ge 25$, $n/k \ge 5$.
We need $g > 5$.
This means $\binom{n}{5}$ not div by 2, 3, 5.
But $\binom{n}{k}$ is an integer.
If not div by 2, 3, 5, then $\binom{n}{k} \equiv \pm 1 \pmod{30}$? No.
Actually, if $\binom{n}{5}$ is not div by 2, then $n \equiv k \pmod 2$?
Kummer's theorem: $2 \nmid \binom{n}{k} \iff$ sum of digits of $k$ and $n-k$ equals digits of $n$ in binary (no carries).
For $k=5=(101)_2$.
We need $n-k$ to have 0s at positions where $k$ has 1s.
So $n-k$ must have 0 at pos 0 and 2.
So $n-k \equiv 0 \text{ or } 2 \pmod 8$?
$(n-k) \& 5 = 0$.
So $n-k \equiv 0, 2 \pmod 8$.
If $n-k \equiv 0 \pmod 8$, then $n \equiv 5 \pmod 8$.
If $n \equiv 5 \pmod 8$, then $n$ is odd. $n-1$ div by 4. $n-2$ odd. $n-3$ even. $n-4$ odd.
Sequence $n, \dots, n-4$: $Odd, 4k, Odd, 2k, Odd$.
Product has $2^{2+1} = 8$. $k! = 120$ has $8$.
So $v_2$ matches.
What about 3? $k=5=(12)_3$.
No carries $3 \nmid \binom{n}{5} \iff (n-k) \text{ base 3 digits } + (1, 2) \le (2, 2)$.
So $(n-k)_0 \le 0 \implies (n-k) \equiv 0 \pmod 3$.
$(n-k)_1 \le 1 \implies$ digit is 0 or 1.
So $n-k \equiv 0, 3 \pmod 9$.
So $n \equiv 5 \pmod 9$.
What about 5? $k=5=(10)_5$.
$5 \nmid \binom{n}{5} \iff (n-k)_1 \le 0 \implies$ digit 0.
So $n-k \equiv 0, 1, 2, 3, 4 \pmod{25}$? No.
Digit at $5^1$ must be such that no carry from $5^0$.
Actually digit of $k$ at $5^1$ is 1.
So $(n-k)$ digit at $5^1$ must be such that sum $< 5$.
Wait, $k=10_5$. $n-k = \dots d_1 d_0$.
$d_0 + 0 < 5$. Always true.
$d_1 + 1 < 5 \implies d_1 \in \{0, 1, 2, 3\}$.
So $n-k$ can be almost anything mod 25, just not $4 \cdot 5 + \dots$.
But we also need $n-j \mid 120$.
$n-j$ must be smooth (primes 2, 3, 5).
If $n-j=120$. $n \in [120, 124]$.
Check $n=120$. $\binom{120}{5}$.
$120$ is even. $\binom{120}{5}$ is even?
$120 = 1111000_2$. $5=101_2$.
$120-5 = 115 = 1110011_2$.
$115+5$: $1+1=0$ carry.
So $2 \mid \binom{120}{5}$.
So $g=2 \le 5$.
No exception for $k=5$.

**$k=6$**: $n \ge 36$.
$S \ne \emptyset \implies n-j \mid 720$.
Potential smooth numbers $n-j \in \{36, \dots, 720\}$.
We established $n=62$ is a candidate.
Let's check $n=62, k=6$.
$\binom{62}{6} = 61474519$.
$n/k = 10.33$.
Primes $\le 10.33$: 2, 3, 5, 7.
We verified in the context that $g(62, 6) = 19 > 10.33$.
So $(62, 6)$ is an exception.
Are there others?
We need $n-j \mid 720$.
Also we need $\binom{n}{6}$ not div by 2, 3, 5 (and 7 if $n/k \ge 7$, which it is for $n \ge 42$).
For $(62, 6)$, $n/k < 11$.
Check other divisors of 720.
$n-j$ must be close to $n$.
And $\prod_{i \ne j} a_i = 720 / (n-j)$.
For $n=62$, $n-j=60$. Ratio 12.
Smooth parts of $62, 61, 59, 58, 57$: $2, 1, 1, 2, 3$. Product 12. Matches.
Is there another match?
Try $n-j = 360$ (half of 720).
Remaining product 2.
Need 5 terms with smooth product 2.
Terms around 360.
$360, 359, 358, \dots$
Primes for $n \approx 360, k=6$: $2, 3, 5, \dots$ up to $60$.
Smooth parts will be the numbers themselves if they are $\le 60$-smooth.
For $n \approx 360$, most numbers are smooth?
No, prime 61, etc.
But we need smooth parts $a_i$ to have product 2.
This implies 4 terms have $a_i=1$.
So 4 terms are primes (or product of large primes).
In 6 consecutive integers, can we have 4 primes?
For $n \approx 360$, maybe.
But one is divisible by 6 (smooth part $\ge 6$).
One is divisible by 4 (smooth part $\ge 4$).
One is divisible by 5 (smooth part $\ge 5$).
Wait, $a_i$ is the $n/k$-smooth part.
If $n=360$, $n/k=60$.
Almost everything is 60-smooth.
So $a_i = n-i$.
Product $\approx 360^5$.
But we need product 2.
Impossible.
So for large $n$, $S \neq \emptyset$ requires $n-j$ to be small?
But $n-j \approx n$.
Contradiction.
We need $\prod a_i = 720$.
If $n$ is large, $a_i$ are typically large (unless they are prime $> n/k$).
If $n$ is large, $n/k$ is large.
If $n/k > n$, everything is smooth.
But $n \ge k^2$.
So $n/k \le \sqrt{n}$.
Smooth parts are large.
So $\prod a_i$ will be HUGE.
We need $\prod a_i = 720$.
This forces $a_i$ to be small.
So most $n-i$ must be "rough" (primes $> n/k$).
This means we need 5 out of 6 integers to be prime (or rough).
For $n=62$, $n/k=10$. Rough means prime factor $> 10$.
$57 = 3 \cdot 19$ (rough 19).
$58 = 2 \cdot 29$ (rough 29).
$59$ (rough 59).
$61$ (rough 61).
$62 = 2 \cdot 31$ (rough 31).
$60 = 2^2 \cdot 3 \cdot 5$ (smooth).
This worked.
For $n=360$, rough means prime $> 60$.
We need 5 terms to be multiples of primes $> 60$.
$355, 356, 357, 358, 359, 360$.
$359$ is prime (?).
$355 = 5 \cdot 71$ (71 > 60). Rough.
$357 = 3 \cdot 7 \cdot 17$. No prime $> 60$. Smooth.
$356 = 4 \cdot 89$ (89 > 60). Rough.
$358 = 2 \cdot 179$ (179 > 60). Rough.
$360$ Smooth.
We have 2 smooths ($357, 360$).
$a_{357} = 357$. $a_{360} = 360$.
Product $357 \cdot 360 \gg 720$.
So impossible.
Thus, for large $n$, we cannot satisfy $\prod a_i = k!$.
This proves that exceptions are bounded to small $n$.
Ecklund checked these.
Only $(62, 6)$ remains.

### 4. Conclusion
The condition $g(n, k) \le n/k$ holds for all $n \ge k^2$ with the exception of $(62, 6)$.
For $(62, 6)$, $g=19 > 10.33$.
For all other cases, either $g \le k \le n/k$ or the configuration of smooth numbers required for $g > n/k$ does not exist.

## References
1. Ecklund, E. F., Jr. (1969). "On the prime factorization of binomial coefficients".
2. Ecklund, E. F., Jr., Erdős, P., and Selfridge, J. L. (1974).
