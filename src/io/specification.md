# Importing/exporting waterproof notebooks from/to vernacular file
We aim to make the exported .v files easy to read, and adhering to coqdoc format for nice coqdoc rendering. We are a bit constrained as we like *exact reproducibility*, though we will settle for approximate reproducibility for the benefit of readability of .v files.


## Block structure

Waterproof notebooks are made out of a collection of blocks, and each has one of the following types of block: text, code, input, and hint block. We translate these blocks according to their type. We choose to get rid of unnecessary metadata, and infer this when re-importing the blocks.
Concretely, a block in waterproof is an object containing a `type` and `text`. If it is an input block, it also contains `start` and `id`. We translate this as follows:
- If it is a code block: simply return `text`. Note that we will not be able to interpret whether two code blocks should be separated.
- If it is a text block: return `(** text *)`.
- If it is a hint block: return `(** HINT text *)`. **And implement in waterproof that the hint-closed text is immutable**
- If it is an input block:
   - with `start == True`: return `(** INPUT-START *)`
   - with `start == False`: return `(** INPUT-END *)` **We could get away with only writing INPUT and inferring whether it is start or end, but this is more informative in .v files in my opinion**

For re-importing, everything we encounter that is not in a `(**` and `*)` is a code block. Originally contiguous code blocks will become one large code blocks. To split these up, you can input an empty text block `(** *)` or even `(***)` (the latter is not rendered in coqdoc, while the former is rendered as an empty line).

## Unintentional comment start/end

Coq uses `(*` and `*)` to denote comment start and end. These can be used recursively. If they are in text and are exported inside a `(** *)`, it will interfere with the formatting.
Unfortunately, it is easy to unintentionally write these. For example, the following waterproof text sentence:

> (Water *proof*) text

is syntactically `(Water *proof*) text`, which inadvertently contains a comment ending in Coq. Therefore, we will add a special character to remove any comment start or end non-code. The above sentence will become `(Water *proof*💧) text`.

## String literals

Moreover, Coq string literals in comments *must* be completed in order to be parsed correctly. Strings begin and end with double quotes (`"`). To avoid an odd number of double quotes, we add an `"` to the end of `text` if it contains only one.

## Using \#{1-6}
In waterproof (markdown) we may start text with `# `, `## `, ..., `###### ` to indicate various levels of headings, but in coqdoc we must use `* `, `** `, `**** `. Hence, we translate `#{1-4} ` at the start of a block to `*{1-4} ` and back to `#{1-4}` again. **If there is `#{5,6}` I don't know what to do yet**.

## Bold/italics
In waterproof (markdown) we may use `**text**` and `*text*` to write bold/italics respectively. In coq, we can do emphasis (italics) with `_text_`. Bold is a bit harder, but we can use `#<strong>#text#</strong>#`.

## Coqdoc escape characters
To simply output the characters $, % and # and escaping their escaping role in coqdoc, these characters are be doubled. In coqdoc, `$text$` would output text in latex math-mode. **However, this does not work for HTML-output, so it is quite useless.** 
It is a little bit of a problem, because stuff in # is simply discarded in latex output actually.
https://coq.inria.fr/refman/using/tools/coqdoc.html#escaping-to-latex-and-html

## Notebook or exercise sheet?

Always import as notebook. So previously exported exercise sheet can become notebook.

***Should this be different? We could import exercise sheets as exercise sheets, but they are mutable as .v files anyways, and this will also complicate the UI***
