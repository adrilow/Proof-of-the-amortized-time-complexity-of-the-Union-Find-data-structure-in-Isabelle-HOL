# Bachelor Thesis: Proof of the amortized time complexity of an efficient implementation of the Union-Find data structure in Isabelle/HOL

For a detailed explanation of the project, as well as the presented theories, see the writeup in ./tum-thesis-latex-master which contains its own README for building the pdf, or the already compiled submitted version of the thesis.

## Usage

These theories have been tested with [Isabelle2018], although the use in more recent versions should be possible.

The files InverseNatNat.thy and Ackermann.thy only need a regular Isabelle2018 setup.

The rest of the theories build upon [Sepreftime], you will need to succesfully set up that project first, and then place this repository as its own directory inside /Sepreftime/Examples.

## License

### For the files in the folder ./tum-thesis-latex-master:

These are distributed under the [Creative Commons Attribution-ShareAlike 4.0 International License][license], meaning that:

 * You can share (copy, redistribute) and adapt (remix, transform, build upon) this template for any purpose, even commercially.
 * If you share the template or a modified (derived) version of it, you must attribute the template to the original authors ([Florian Walch and contributors][template-authors]), by providing a [link to the original template][template-url] and indicate if changes were made.
 * Any derived template has to use the [same][license] or a [compatible license][license-compatible].

The license **applies only to the template**.

* The resulting PDF file and the contents of the thesis are licensed under the [Creative Commons Attribution-ShareAlike 4.0 International License][license] for which the original author is Adrián Löwenberg Casas and the link to the original work is this repository.


### For the theories Ackermann.thy and InverseNatNat.thy:

These works are original work by Adrián Löwenberg Casas distributed under the [2-clause-BSD] license, see LICENSE.md.

### For the rest of the theories:

These are derived work from the work by M. P.L. Haslbeck and Peter Lammich found in [Sepreftime], and are distributed further under the [2-clause-BSD] license, see LICENSE.md.



[Isabelle2018]: https://isabelle.in.tum.de/website-Isabelle2018/index.html
[Sepreftime]: https://www21.in.tum.de/~haslbema/Sepreftime/
[2-clause-BSD]: https://opensource.org/licenses/BSD-2-Clause

[license-compatible]: https://creativecommons.org/compatiblelicenses
[license-image]: https://i.creativecommons.org/l/by-sa/4.0/88x31.png
[license]: https://creativecommons.org/licenses/by-sa/4.0/
[template-url]: https://github.com/fwalch/tum-thesis-latex

