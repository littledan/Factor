USING: help.markup help.syntax sequences math ;
IN: bit-sets

ARTICLE: "bit-sets" "Bit sets"
"The " { $vocab-link "bit-sets" } " vocabulary implements bit-array-backed sets. Bitsets are efficient for implementing relatively dense sets whose members are in a contiguous range of integers starting from 0. One bit is required for each integer in this range in the underlying representation."
"Bit sets are of the class"
{ $subsection bit-set }
"They can be instantiated with the word"
{ $subsection <bit-set> } ;

ABOUT: "bit-sets"

HELP: bit-set
{ $class-description "The class of bit-array-based sets. These implement the " { $link "sets" } "." } ;

HELP: <bit-set>
{ $values { "capacity" integer } { "bit-set" bit-set } }
{ $description "Creates a new bit set with the given capacity. This set is initially empty and can contain as members integers between 0 and " { $snippet "capacity" } "-1." } ;
