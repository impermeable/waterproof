# Importing/exporting waterproof notebooks from/to vernacular file
We aim to make the exported .v files easy to read, and adhering to coqdoc format for nice coqdoc rendering. We are a bit constrained as we like *exact reproducibility*, though we will settle for approximate reproducibility for the benefit of readability of .v files.

## Waterproof notebooks and exercise sheets

Waterproof notebooks and exercise sheets are practically `.json` files, but have extensions `.wpn` and `.wpe` respectively. The files have two attributes, `exerciseSheet` and `blocks`. For a notebook, `exerciseSheet : false` and for an exercise sheet, `exerciseSheet : true`. 
The blocks attribute is a sequence of dictionaries. Every element in the sequence contains:

- a field `type`, which is one of: `text`, `code`, `input` or `hint`.
- a field `text`, which contains the content of the block
- a field `id`, which is present if and only if the field is an input block, which contains a unique identifier for the block
- a field `start`, which is present if and only if the field is an input block, which encodes whether this is the start or the end of an input block

## Exporting to `.v` file

We export a notebook or exercisesheet to a `.v` file as follows:

- If it is a code block: simply return the content stored in the field `text`. Between the output of two consecutive code blocks, we add `(***)`.
- If it is a text block: return `(** convert_to_valid(text) *)`.
- If it is a hint block: return `(** convert_to_valid(text_before_first_<hint>)\n<hint>\nconvert_to_valid(text_after_first_<hint>)*)`.
- If it is an input block:
   - with `start == True`: return `(** INPUT-START *)`
   - with `start == False`: return `(** INPUT-END *)` **We could get away with only writing INPUT and inferring whether it is start or end, but this is more informative in .v files in my opinion**
- Make (separate) settings whether $, %, and/or # occurring in hint or text blocks need to be doubled on export

For re-importing, everything we encounter that is not in a `(**` and `*)` is a code block. Originally contiguous code blocks will become one large code blocks. To split these up, you can input an empty text block `(** *)` or even `(***)` (the latter is not rendered in coqdoc, while the former is rendered as an empty line).

## Importing to `.v` file

- The (outer-layer) coqdoc comments `(** INPUT-START *)` and `(** INPUT-END *)` are mapped to blocks with type `input`
- Outer-layer coqdoc comments that somewhere contain `<hint>` are converted to hint blocks.
- Every other outmost-layer coqdoc comment gets assigned an input block type `text` with contents of the coqdoc comment.
- The `id` of the `n`th imported input block is assigned `input-n`
- Open input blocks get closed before a next input block is opened, additional closures of input blocks are ignored
- If no text is present before `<hint>` in open hint block, then add standard text: Click to open hint.
- Note: text is not stripped
- Make (separate) settings whether $, %, and/or # occurring in hint or text blocks need to be halved on import

## Conversion to valid text

Decision/aim: stay as close as possible to coqdoc notation in the json file. Only in rendering go to the markdown dialect.

The function `convert_to_valid` performs the following actions:

- Close string literal at the end of the markdown block (if one is open at the end)
- Close all open comments at the end of the markdown block
- Open comments at the beginning of the markdown block

### Waterproof conversions:

Convert in rendering (in the `render` function in `WpBlock.vue`)

- `(*` to `(💧` and `*)` to `💧)`, where precedence goes from left to right.
- Header-*'s to #'s
- `#<strong>#` and `#</strong>#` both to `**`
- Consecutive `[` and `]` both to backticks.
- \_arbitrary text\_ to \*arbitrary text\* if \_ preceded by a whitespace or followed by a whitespace or punctuation.
- If markdown lists with '*' don't work: Coqdoc lists (with '-') to markdown lists (with '*')

---

Old stuff:

### Unintentional comment start/end

Coq uses `(*` and `*)` to denote comment start and end. These can be used recursively. If they are in text and are exported inside a `(** *)`, it will interfere with the formatting.
Unfortunately, it is easy to unintentionally write these. For example, the following waterproof text sentence:

> (Water *proof*) text

is syntactically `(Water *proof*) text`, which inadvertently contains a comment ending in Coq. Therefore, we will add a special character to remove any comment start or end non-code. The above sentence will become `(Water *proof*💧) text`.

TODO: maybe need to start enforcing matching of comments in Waterproof

### String literals

In CoQ, if a string literal is opened in a comment, everything that follows after it until the string literal is closed is considered part of the string and has no further syntactic interpretation.

Moreover, Coq string literals in comments *must* be completed in order to be parsed correctly. Strings begin and end with double quotes (`"`). To avoid an odd number of double quotes, we add an `"` to the end of the open comment in `text` if it contains an odd number of quotes.

### Using \#{1-6}
TODO: in principle we can ignore(?) this and tackle it in the Vue representation of blocks.
In waterproof (markdown) we may start text with `# `, `## `, ..., `###### ` to indicate various levels of headings, but in coqdoc we must use `* `, `** `, `**** `. Hence, we translate `#{1-4} ` at the start of a block to `*{1-4} ` and back to `#{1-4}` again. **If there is `#{5,6}` I don't know what to do yet**.

### Bold/italics
In waterproof (markdown) we may use `**text**` and `*text*` to write bold/italics respectively. In coq, we can do emphasis (italics) with `_text_`. Bold is a bit harder, but we can use `#<strong>#text#</strong>#`.

### Coqdoc escape characters
To simply output the characters $, % and # and escaping their escaping role in coqdoc, these characters are be doubled. In coqdoc, `$text$` would output text in latex math-mode. **However, this does not work for HTML-output, so it is quite useless.** 
It is a little bit of a problem, because stuff in # is simply discarded in latex output actually.
https://coq.inria.fr/refman/using/tools/coqdoc.html#escaping-to-latex-and-html

### Notebook or exercise sheet?

Always import as notebook. So previously exported exercise sheet can become notebook.

***Should this be different? We could import exercise sheets as exercise sheets, but they are mutable as .v files anyways, and this will also complicate the UI***
