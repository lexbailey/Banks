# An implementation of (the working bits of) Banks's Confidentiality Framework

In 2012, Michael Banks's PhD thesis was published, in which he introduced a framework for modelling confidentiality on top of Unifying Theories of Programming (UTP)[1]

Unfortunately, it was not checked using a theorem prover, and thus some errors are present in the work.

This repo contains my attempt to encode Banks's framework inside Isabelle/UTP[2,3]

Rather than encoding all of Banks's framework, I had to settle for encoding some of it, and then proving why I couldn't continue. There is an error fairly early on in the work. Instead I have used Isabelle/UTP to prove that there is indeed a flaw in Banks's work that prevents me implementing it as-is.

My work to provide a framework inside Isabelle/UTP for considering confidentiality properties will continue in a different direction.

## Files

`Banks/banks.thy` contains most of the proofs that did work, and also the proof that one of Banks's proofs doesn't hold

`examples/*.thy` are recreations of the early examples from Banks's work that are indeed correct and can be proved

## References

[1] M. J. Banks, ‘On Confidentiality and Formal Methods’, PhD Thesis, University of York, University of York, 2012. Accessed: Nov. 22, 2022. [Online]. Available: http://etheses.whiterose.ac.uk/2709/

[2] S. Foster, F. Zeyda, Y. Nemouchi, P. Ribeiro, and B. Wolff, ‘Isabelle/UTP: Mechanised Theory Engineering for Unifying Theories of Programming’, Archive of Formal Proofs, Feb. 2019.

[3] Isabelle/UTP website: https://isabelle-utp.york.ac.uk/
