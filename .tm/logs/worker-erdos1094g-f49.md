# timtam Task: Prove Sylvester-Schur Theorem: n > k implies prime factor p > k (erdos1094g-f49)

Role: explore
Agent: explore (google-antigravity/gemini-3-pro-high:high)
Start Time: 2026-02-08T20:39:48.917Z

## Agent Interaction



> **Thinking:**
> **Checking for Prior Proofs**
> 
> I'm currently looking into whether the Sylvester-Schur Theorem, specifically the claim that $n > k \implies \binom{n}{k}$ has a prime factor $p > k$, or its generalization of Bertrand's Postulate, is already proven in Mathlib or the `proofs/` directory. If so, my next steps may be different.
> 
> 
> 


```bash
$ ls -F
```

```bash
$ ls -F proofs/
```

```bash
$ grep -r "Sylvester" .
```


> **Thinking:**
> **Reviewing Erdos/Sylvester.lean**
> 
> I'm currently focused on the `Erdos/Sylvester.lean` file. I've noted that it houses `Erdos1094.sylvester_theorem`. For now, I've got that a proof exists for the $n=2k$ case, which relies on Bertrand's Postulate.
> 
> 
> **Analyzing Axiom Usage**
> 
> I've realized the current implementation relies on an axiom (`sylvester_schur_theorem`) for the $n > 2k$ case, which conflicts with the project's goal of avoiding axioms. The task specifies I should craft a non-axiomatic proof. I will therefore check Mathlib for the required functionality. If unsuccessful, a rigorous natural language proof will be crafted in `proofs/sylvester.md`.
> 
> 
> **Confirming Non-Existence in Mathlib**
> 
> I've confirmed my suspicion: the full Sylvester-Schur theorem isn't readily available in Mathlib, or at least it hasn't been found. Bertrand's Postulate, a special case, is present. Thus, I must proceed with crafting a natural language proof for the general case within `proofs/sylvester.md`. I have a clear understanding of the theorem's statement.
> 
> 
> **Developing Erdos's Proof**
> 
> I'm now diving deep into Erdos's proof. The core idea focuses on the product of $k$ consecutive integers and demonstrating divisibility by a prime $p > k$. It's a non-trivial endeavor, similar to Bertrand's Postulate's proof but more general. The strategy will involve assuming the contrary, analyzing the prime factorization of binomial coefficients, and applying estimates for prime counting functions. My next step involves drafting `proofs/sylvester.md`, referencing Erdos's 1934 paper. I've verified the file doesn't currently exist.
> 
> 
> **Refining Erdos's Strategy**
> 
> I'm now refining my approach to Erdos's proof, focusing on the product $u_k = n(n-1)...(n-k+1)$. I'm considering the implications of assuming all prime factors of $u_k$ are less than or equal to $k$. My exploration involves Legendre's formula, the exponent of primes in binomial coefficients, and carries in base-p addition. I aim to leverage these concepts to contradict the initial assumption. Currently I am focusing on sticking to Erdos's proof.
> 
> 
> **Investigating Interval Properties**
> 
> I'm now investigating prime number distributions within specific intervals. I am focused on applying Bertrand's Postulate, but I'm considering its implications with the assumption of $k \le n < 2k$ to the Sylvester-Schur proof. The goal is to determine the presence of a prime factor $p$ within a crucial interval and its subsequent impact on the binomial coefficient's divisibility. The work involves considering the ratio of factorials and the potential for cancellation of prime factors.
> 
> 
> **Clarifying Interval Conditions**
> 
> I'm now clarifying the interval conditions related to Sylvester's theorem, in the $n > 2k$ case, the prime $p > k$ does not need to be within the interval $[n-k+1, n]$, but rather the crucial condition for divisibility of the binomial coefficient. I can move on to outlining the steps of Erdos's proof.
> 
> I will write the proof following Erdos's argument, beginning by focusing on the case where $n \le 2k$ to develop a clear foundation for the proof. I will then examine the general case.
> 
> 
> **Revisiting Sylvester's Statement**
> 
> I'm now revisiting the core statement of Sylvester's theorem, carefully parsing the conditions. It's crucial to ensure my understanding aligns perfectly with the intended meaning. I realize now that the theorem requires that $n-k+1 > k$, which translates to $n > 2k - 1$. This means the condition $n > k$ isn't sufficient. This implies a need to clarify this condition in my proof.
> 
> 
> **Refining Condition Implications**
> 
> I'm now refining my understanding of Sylvester's theorem, focusing on the implications of the conditions involved. The theorem states $n > k$ implies a prime factor $p > k$. However, the key is the precise meaning of this and I need to be more precise about this condition. My current understanding means that in the binomial coefficient $\binom{n}{k}$, where $n > k$, there exists a prime $p > k$ that divides it. I am trying to determine if it always does. I am trying to determine where it fails, as in cases where $n < 2k$ the binomial coefficient can be smaller than that.
> 
> 
> 
> **Clarifying Theorem Assumptions**
> 
> I'm now clarifying a crucial point about the theorem's assumptions, since my prior thoughts were wrong. The theorem, in its standard form and as formalized in `Erdos/Basic.lean`, requires $n \ge 2k$, not just $n > k$. I was mistaken on this point in my previous thoughts. I've been reviewing the formalization and the prompt. This nuance is critical, as the theorem doesn't hold for all $n > k$. I'll explicitly address this restriction, and begin outlining Erdos's non-axiomatic proof.
> 
> 
> **Outlining Erdos' Proof**
> 
> I am now outlining Erdos's non-axiomatic proof. I'm focusing on the case where $n \ge 2k$. I plan to use the standard steps for the proof, beginning with a proof statement. I will need to use Legendre's formula. I'm focusing on the core assumption, that if the prime $p > k$ does not divide the binomial coefficient $\binom{n}{k}$, it simplifies the binomial coefficient into a product of primes $p \le k$. I'm exploring an upper bound for the binomial coefficient, which involves comparing its magnitude with estimates from the prime-counting function and Legendre's formula. The central logic will involve arriving at a contradiction for large values of $n$ and $k$, by proving that the binomial coefficient's size, based on its prime factors less than or equal to $k$, is too small. I think this will work.
> 
> 
> 


🛠️ **Executing tool: read**


> **Thinking:**
> **Refining Axiom Utilization**
> 
> I've just observed that the `Erdos/Sylvester.lean` file employs `axiom sylvester_schur_theorem` to address scenarios where $n > 2k$. The axiom's definition, `axiom sylvester_schur_theorem (n k : ℕ) (h : n > k) : ∃ p, p.Prime ∧ p ∣ n.choose k ∧ p > k`, aligns perfectly with the problem's requirements. Now, considering...
> 
> 
> **Correcting Axiom Usage**
> 
> I've determined the `sylvester_schur_theorem` axiom is false for `n` close to `k`, specifically when `n < 2k`. I previously saw the axiom in `Erdos/Sylvester.lean` and focused on the condition `n > k`. Although the axiom is flawed, the main `sylvester_theorem` restricts its usage to `2 * k ≤ n`, which makes the usage safe. However, the faulty axiom is bad. Now, I will update.
> 
> 
> **Formulating Proof Strategy**
> 
> I'm now outlining the steps for `proofs/sylvester.md`. The plan is to adopt Erdos's approach. First, I'll state the theorem clearly: For $n \ge 2k$, the binomial coefficient $\binom{n}{k}$ has a prime factor $p > k$. The proof will begin by using Erdos's proof. This involves handling the case where $k$ is small, either manually or by citing verified exceptions. Then, I'll assume all prime factors of the binomial coefficient are $\le k$ to derive a contradiction. I'll focus on bounding the binomial coefficient and demonstrating this contradiction for sufficiently large $k$. I've also identified a crucial connection: Erdos's proof, by showing that a product of $k$ consecutive integers contains a prime $p>k$, implies that prime $p$ also divides the binomial coefficient because $p$ does not divide $k!$. I'm ready to start writing.
> 
> 
> **Implementing Proof and Fix**
> 
> I'm now writing the proof in `/sylvester.md`, following Erdos's approach. My focus is handling both the small k cases and the large k cases. I am also preparing to bound the binomial coefficient. I decided I should correct the flawed axiom in `Erdos/Sylvester.lean`. I will restrict the axiom to `n >= 2k`.
> 
> 
> **Refining Proof Structure**
> 
> I'm now diving into the details of Erdos's proof from the 1934 paper. I've confirmed the theorem states that for $n \ge 2k$, the product of $k$ consecutive integers contains a prime greater than $k$. The paper's approach to the binomial coefficient $\binom{n}{k}$ is now being carefully analyzed. The core will be contradiction by assuming that all primes in the binomial coefficients are $\leq k$. I must now focus on applying this to get an explicit proof.
> 
> 
> **Evaluating Prime Factorization**
> 
> I'm now focusing on bounding $\nu_p(\binom{n}{k})$, specifically using Legendre's formula to dissect the prime factorization. I can now express $\nu_p(\binom{n}{k})$ as a sum involving floor functions. It appears that $\nu_p(\binom{n}{k}) \leq \log_p n$, which yields an upper bound on the power of $p$ in the binomial coefficient. I'm carefully analyzing the impact of prime $p > \sqrt{n}$ versus $p \leq \sqrt{n}$ for tighter bounds. I think I'm making good progress.
> 
> 
> **Analyzing Bounds and Cases**
> 
> I'm now investigating specific bounds on the binomial coefficient, especially for Bertrand's postulate case ($n=2k$). I see the connection to the 1934 paper and Erdos's methods, focusing on prime factors. I'm focusing on the case when $n \ge 2k$. I am going to bound $\binom{n}{k} \le n^{\pi(k)}$ and $\binom{n}{k} \ge (\frac{n}{k})^k$, and will consider the cases and split. I'll utilize Sylvester-Schur's observation for a contradiction.
> 
> 
> **Developing Proof Strategy**
> 
> I'm now integrating the prime factorization ideas into the proof structure. I am now focused on an assumption: If, for any prime factor, a sequence of $k$ consecutive integers contains only primes $\le k$, this leads to a contradiction. Specifically, I'm examining how many times a prime $p$ and its powers can divide these terms. The key observation is that $p^\alpha$ divides at most $\lceil k/p^\alpha \rceil$ terms within this sequence. I will have to clarify the distinction when $k \le n < 2k$ in the writeup. I can now restrict the proof to $n \ge 2k$. I'm almost ready to put the proof down in writing.
> 
> 
> 


🛠️ **Executing tool: write**


> **Thinking:**
> **Checking Task Details**
> 
> I've just finished writing the proof in `proofs/sylvester.md`. But, before I formally mark the status as complete, I'm quickly double-checking the task details. I'm focusing on the ID, priority and most importantly the precise goal, as outlined in the task. It's: "Prove that for n > k, binomial(n, k) has a prime factor p > k." This generalizes Bertrand.
> 
> 
> 


🛠️ **Executing tool: edit**


> **Thinking:**
> **Refining Sylvester's Application**
> 
> I'm currently updating the `Erdos/Sylvester.lean` file, specifically the `sylvester_schur_theorem` usage. Initially, the proof used `exact sylvester_schur_theorem n k h_nk`. I'm now aiming for the condition `2 * k \le n`. I have the hypothesis `h_gt : 2 * k < n` in `Case 2`, and now must utilize it to satisfy that condition.
> 
> 
> 


🛠️ **Executing tool: edit**


> **Thinking:**
> **Updating the axiom definition**
> 
> I've revised the `sylvester_schur_theorem` axiom. The comment and signature have been updated. I edited the comment initially, but there was an issue with the usage of `h_nk`, so I replaced it with `(le_of_lt h_gt)`.
> 
> 
> 


```bash
$ lake build
```


> **Thinking:**
> **Confirming Implementation Progress**
> 
> I'm pleased to report a successful compilation; `Erdos.Sylvester` built flawlessly in 2.0 seconds. The code now includes an axiom `sylvester_schur_theorem` and a related theorem within `Erdos.Sylvester.lean`. There are no warnings (beyond expected `sorry` instances).
> 
> 
> 


🛠️ **Executing tool: read**


> **Thinking:**
> **Reviewing Sylvester's Theorem**
> 
> I've addressed the Sylvester-Schur theorem's axiom by constraining it as `n >= 2k`. I've verified the `Erdos.Sylvester` component is clean, albeit reliant on an axiom. Notably, the build log's `sorry` warnings stemmed from `Erdos.Ecklund` and `Erdos.EES1974`, not my specific file.
> 
> 
> 


```bash
$ tm update erdos1094g-f49 --status "Completed NL proof in proofs/sylvester.md and fixed axiom in Erdos/Sylvester.lean"
```
The Sylvester-Schur Theorem (1892) generalizes Bertrand's Postulate, stating that the product of $k$ consecutive integers greater than $k$ contains a prime factor greater than $k$. In terms of binomial coefficients, this implies that for $n \ge 2k$, $\binom{n}{k}$ has a prime factor $p > k$.

I have created a rigorous natural language proof in `proofs/sylvester.md`, following the method of Paul Erdős (1934). I also identified that the existing axiom in `Erdos/Sylvester.lean` was unsound as stated (claiming the result for $n > k$ generally, which fails for $k < n < 2k$) and corrected it to require $n \ge 2k$, ensuring the codebase is mathematically sound.

```json
{
  "status": "completed",
  "summary": "Proved Sylvester-Schur Theorem in proofs/sylvester.md and corrected the axiom in Erdos/Sylvester.lean.",
  "details": "1. Created `proofs/sylvester.md` with a rigorous proof for `n >= 2k` based on Erdős (1934), using Legendre's formula and bounds on prime products.\n2. Identified that the statement `n > k implies p > k` is false for `k < n < 2k` (e.g., `C(4,3)=4`).\n3. Corrected `axiom sylvester_schur_theorem` in `Erdos/Sylvester.lean` to require `2 * k <= n`, ensuring soundness.\n4. Updated the proof of `sylvester_theorem` to use the corrected axiom."
}
```

## Final Result

The Sylvester-Schur Theorem (1892) generalizes Bertrand's Postulate, stating that the product of $k$ consecutive integers greater than $k$ contains a prime factor greater than $k$. In terms of binomial coefficients, this implies that for $n \ge 2k$, $\binom{n}{k}$ has a prime factor $p > k$.

I have created a rigorous natural language proof in `proofs/sylvester.md`, following the method of Paul Erdős (1934). I also identified that the existing axiom in `Erdos/Sylvester.lean` was unsound as stated (claiming the result for $n > k$ generally, which fails for $k < n < 2k$) and corrected it to require $n \ge 2k$, ensuring the codebase is mathematically sound.

```json
{
  "status": "completed",
  "summary": "Proved Sylvester-Schur Theorem in proofs/sylvester.md and corrected the axiom in Erdos/Sylvester.lean.",
  "details": "1. Created `proofs/sylvester.md` with a rigorous proof for `n >= 2k` based on Erdős (1934), using Legendre's formula and bounds on prime products.\n2. Identified that the statement `n > k implies p > k` is false for `k < n < 2k` (e.g., `C(4,3)=4`).\n3. Corrected `axiom sylvester_schur_theorem` in `Erdos/Sylvester.lean` to require `2 * k <= n`, ensuring soundness.\n4. Updated the proof of `sylvester_theorem` to use the corrected axiom."
}
```

End Time: 2026-02-08T20:42:12.994Z
