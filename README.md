# Atlas

Atlas is the following:

1. A toolset for formalizing existing literature, maintaining flow with the source and formalization target and
   recording metadata along the way.
2. A toolset for displaying, querying, and understanding the metadata provided
3. A toolset for extending that dataset in a manner optimized for mathematicians moreso than programmers.
4. A set of widgets for surfacing that metadata at prooftime
5. Tools for tracking the changes to the implied 'theorem graph' over the course of a project.
6. Editor extensions for at least vim to make things smooth and simple to use.

Atlas provides a custom syntax for annotating and defining theorems, and provides lots of tools for controlling how
those theorems are referenced, how they are grouped together, and how they are displayed in the final server.

The goal of Atlas isn't necessarily to be From The Book, rather, Atlas aspires to be the tool The Book is written
_with_; as well as a tool to help the Author write theorems that are well documented, well explained, and easy to
understand.

## Syntax Extensions

Here's an example of a real theorem documented with Atlas:

```lean4
atlas commentary := by
  ref proposition 3.4
  page 113
  name "Line Separation Property"
  aliases [
    Geometry.Theory.Line.separation
  ]
  preface "If C - A - B and l is the line through A, B, and C (Betweenness Axiom 1), then for every point P lying on l, P lies either on ray A B or on the opposite ray A C."

atlas proposition 3.4 "Line separation by an interior point: points on the line lie on one of two opposite rays"
  {A B C P : Point} (CAB : C - A - B) (PonL : P on (line A B)) : P on ray A B ∨ P on ray A C := by
  comment "Some mise en place"
  clearly A ≠ P; clearly B ≠ P; clearly C ≠ P
  have distinctABCP : distinct A B C P := by
    have dABC : distinct A B C := (ref lemma 1.0.39 CAB).of_eq obvious
    separate
    distinguish
    repeat assumption
  have AneB : A ≠ B := by distinguish
  have colABCP : collinear A B C P := by
    have cABC : collinear A B C := (ref lemma 1.0.40 CAB).of_eq obvious
    have ABisSameLine : line A B = cABC.line := ref lemma 2.0.2 AneB
      ⟨ref lemma 1.0.23, cABC.mem A, ref lemma 1.0.24, cABC.mem B⟩
    rw [ABisSameLine] at PonL
    exact (Collinear.insert cABC PonL).of_eq obvious
  comment "Expose the pairwise inequalities for the `forgetting` casts below."
  separate at distinctABCP
  quoting (1) "Either P lies on ray A B or it does not (Law of the Excluded Middle)"
  rcases Classical.em (P on ray A B) with PonRayAB | PoffRayAB
  · quoting (2) "If P does lie on ray A B, we are done" ...
    left; trivial
  · quoting ... "so assume it doesn't; then P - A - B (Betweenness Axiom 3)"
    have PAB : P - A - B := by
      have h := ref axiom B.3 P A B ⟨distinctABCP forgetting C, colABCP forgetting C⟩
      rcases h with ⟨PAB,_,_⟩ | ⟨_,APB,_⟩ | ⟨_, _, ABP⟩
      · exact PAB
      · have PonSegAB : P on segment A B := obvious
        apply ref lemma 2.0.4 at PonSegAB
        contradiction
      · have PonRayAB : P on ray A B := obvious
        contradiction
    quoting (3) "If P = C" ...
    rcases Classical.em (P = C) with PeqC | PneC
    · quoting ... "then P lies on ray A C (by definition)" ...
      obvious
    · quoting ... "so assume P ≠ C; then exactly one of the relations C-A-P, C-P-A, or P-C-A holds (Betweeness Axiom 3 again)."
      have hCAP := ref axiom B.3 C A P ⟨distinctABCP forgetting B, colABCP forgetting B⟩
      quoting (4) "Suppose the relation C-A-P holds (RAA Hypothesis)"
      rcases Classical.em (C - A - P) with CAP | nCAP
      · quoting (5) "We know (by Betweenness Axiom 3) that exactly one of the relations P-C-B, C-P-B, or C-B-P holds."
        have hPBC := ref axiom B.3 P B C ⟨distinctABCP forgetting A, colABCP forgetting A⟩
        rcases hPBC with ⟨PBC,_,_⟩ | ⟨_,BPC,_⟩ | ⟨_, _, PCB⟩
        · quoting (6) "If P-B-C, then combining this with P-A-B (step 2) gives A-B-C (Proposition 3.3), contradiction the
              hypothesis."
          exfalso
          exact ref lemma 1.0.38 ⟨via proposition 3.3.i ⟨PAB, PBC⟩, CAB⟩
        · quoting (7) "If C-P-B, then combining this with C-A-P (step 4) gives A-P-B (Proposition 3.3), contradiction step 2."
          exfalso
          exact ref lemma 1.0.36 ⟨via proposition 3.3.i ⟨CAP, (BPC.symm)⟩, PAB⟩
        · quoting (8) "If B-C-P, then combining this with B-A-C (hypothesis and Betweenness Axiom 1) gives A-C-P (Proposition 3.3),
             contradicting step 4."
          exfalso
          exact ref lemma 1.0.36 ⟨via proposition 3.3.i ⟨CAB.symm, PCB.symm⟩, CAP⟩
      · quoting (9) "Since we obtain a contradiction in all three cases, C-A-P does not hold (RAA conclusion)."
        comment "this is covered by the above .em elimination"
        quoting (10) "Therefore, C-P-A or P-C-A (step 3), which means that P lies on the opposite ray A C. ∎"
        rcases hCAP with ⟨CAP,_,_⟩ | ⟨_,ACP,_⟩ | ⟨_,_,CPA⟩
        · comment "covered above"
          contradiction
        · have PonRayAC : P on ray A C := by obvious
          right; trivial
        · have PonSegAB : P on segment A C := by obvious
          apply ref lemma 2.0.4 at PonSegAB
          right; trivial
```

The rendering components of Atlas use the inline information, the metacommentary, and the proof itself to show a rich
display, with the `quoting` `comment` and other info sections being displayed next to a filtered proof (omitting
aforementioned invokes to minimize the noise) and aligning the line numbers so that it is clear which human steps
(`quoting` if copying from a book, or some other flavor for general explanation) correspond to which lines of Lean code.

It will also show LaTeX markup for the proof statement, any prefacing text, some stats about tactic usage in the proof,
performance information (if gathered), and most importantly, it shows _connections to other referenced theory_ via the
Theory Graph.

The syntax here also allows for two special theorem lookup tools; within your code you can use `ref` and `via` (the
slight semantic differences are explained elsewhere) to refer to theorems by name, index number, or any of their
aliases; in addition to the 'normal' direct reference in Lean. This also allows for theorem _complexes_, these are small
collections of theorems (similar to a simp set) that capture the idea of 'by this theorem or one of its corollaries or
alternatives', and perform a much shorter search than a `simp` or `aesop` might. Theorem complexes can come with custom
`applicator`s, which can encapsulate common arguments that involve that complex of theorems.

## The Theory Graph

Existing tools like Blueprint surface something like this, but where Blueprint is a roadmap that is human authored,
Atlas is a _survey_ of what is already _done_.

Atlas does a second build step after the primary one, importing each module and re-elaborating it to collect the
metadata it needs. This is not particularly speedy and may be quite memory hungry, so it really expects to be run on a
CI server as a 'on merge to main' project. It dumps this information into a `kuzu` graph database which is then embedded
into the viewer for live queries of the codebase. Each of the syntax extensions above feed metadata into the graph,
including which theorems are referenced directly, which tactics are used, what SHA the proof comes from (or a pointer if
it is unchanged between SHAs), etc.

Atlas provides some direct tooling for executing Cypher queries on this graph, as well as canned queries. It also
provides facilities for recording `todo` `fixme` and other implementation-level items into the code; both to make it
easy to filter, but also so these are exposed in the graph and may be queried.

The main product of atlas is actually this graph, all the visualization is stuff built from this graph. The queries
interact with this graph and the point of it is to gather as much metadata about your proofs as possible to make
structural understanding tractable, so that structural refactoring is easier.

## The Atlas View

This renders all your individual theorems as 'cards' containing their formal proof, all the commentary you include in a
side-by-side format, any associated figures, metadata about the proof, and links to other theorems the proof refers too.

This view scales theorems by their importance (via pagerank) and arranges them in layers with axioms at the bottom and
theory growing up from it. This gives a rich overview of each theorem and all its metadata. It is searchable,
filterable, and displays which items are `sorry`ed away. It _does not_ show **expected** dependencies like blueprint,
only _actual_ dependencies by reference. So if you know that, e.g., your margin-scale proof of Fermat references this
obscure work by a guy named Wiles (1995), it won't show up till you actually reference it in the proof; distinct from
Blueprint.

## Who is this for?

Me, mostly. I built it while working on a formalization of _Euclidean and Noneuclidean Geometry_ by Marvin Jay
Greenberg. I wanted to be able to see the structure of my proofs in the context of the piles of theory I'd built, and in
particular find and eliminate dead theory. As I went, I kept finding little things to add, until this came out at the
end.

I hope that it will be useful for three main purposes:

### Formalization of existing work.

Extensive tooling is in place for directly quoting books and rendering it in the graph. Formalizing existing texts is,
by attestation, a great way to learn Lean, and is the primary use case for this library. As mentioned I've driven much
of its design from a real formalization case; and I intend to jump right into another one after I'm done with that.

### Writing textbooks with first-class formalizations

A tool useful for formalizing existing works is barely different than one designed for writing new ones. Atlas should be
able to help arrange texts into logical chunks, keep theory and implementation aligned, and help draw attention to
critical elements of your theory.

### Exploring existing work

Atlas allows for 'external use'; whereby an interested party tags existing Lean code in a noninvasive way, adding all
the relevant theorem-level metadata to the proof. Leaving only the proof-level tags missing. This gets you most of the
way there and still allows for some level of dependency introspection. This lets you easily incorporate other theory
into your project and still get it in the graph, have it be queryable, etc.

-----

A secret fourth thing; a tool for obviating the need for much of the module/namespace chicanery that is currently a
necessary evil in Lean. Atlas may someday include an embedded _editor_ and proof environment so that you can step
through proofs 'live' in the graph, commit them there, and the result will be Atlas _reversing_ the graph into a
canonical representation that sets up all the relevant aliases and so on.

# Atlas CLI

Atlas provides tooling to do all of this

    description of CLI here


# Policy on LLM/Agent use

Atlas is designed by humans, the current implementation is about 80/20 agent/human. Over time I expect that ratio to
balance, but probably never exceed 50/50. I'd regard what's here today as a cardboard prototype for a future version.
Use with caution.

The Corpus and Mereology tests have an initial pass that is entirely LLM driven and likely to not recieve further
attention beyond finishing the formalization of Mereology to fully exercise the tool. Doing a full and proper
formalization of, e.g., the Casati/Varzi text is probably out of scope. I would welcome a proper replacement done by a
human with commentary, maybe I'll get to it some day.

Agents are used extensively for mechanical refactors, syntax hacking, and extending implementations of code initially
written by me. I also consult with them on details of the Lean API frequently.

# LICENSE

Atlas is available under the terms of AGPLv3
