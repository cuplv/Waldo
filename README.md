# Waldo: A library for specifying and proving indistinguishability properties in F*

![Waldo Logo](images/LandofWaldos.jpeg)[^1]

Waldo is a library in F* that helps verify function indistinguishability with
respect to private inputs. If a function soundly models a protocol, Waldo can then be
used to ensure that the protocol guarantees indistinguishability with respect to
Waldo's model.

Learn more about Waldo in our paper: [Verifying Indistinguishability of Privacy-Preserving Protocols](https://kirby.linvill.net/pdfs/indistinguishability_paper.pdf)

## What is indistinguishability?
A function (resp. protocol) is indistinguishable if, for all possible results,
it has an equal probability of producing the result (resp. a given message
trace) regardless of its private inputs. In practice some information, such as
the IP address of a proxy, does not need to be hidden from observers. Such
information is considered public inputs in Waldo. Waldo only verifies
indistinguishability of a function with respect to its private inputs.

[^1]: Image courtesy of
[https://waldo.fandom.com/wiki/The_Land_of_Waldos](https://waldo.fandom.com/wiki/The_Land_of_Waldos)
under the [CC BC-SA license](https://creativecommons.org/licenses/by-sa/3.0/).
