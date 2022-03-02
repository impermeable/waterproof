# Importing/exporting waterproof notebooks from/to vernacular file

We aim to maintain consistent files when importing a previously exported file, with no loss of content.


## Block structure

Waterproof notebooks are made out of a collection of text, code, input, and hint blocks. When exporting to a vernacular file, we do not want to lose this block information, so that the file can be imported again and the structure is maintained. Therefore, a waterproof block is translated to Coq as:
> `(** (*[data]*)[text] *)[code]`

Where `[data]` is the json data contained in the waterproof notebook except the
text or code, and `[text]` and `[code]` are the text and code respectively.
We can accept some variability in terms of 

## Unintentional comment start/end

Coq uses `(*` and `*)` to denote comment start and end.
These can be used recursively.
Unfortunately, it is easy to unintentionally write these.
For example, the following waterproof text sentence:

> (Water *proof*) text

is syntactically `(Water *proof*) text`, which inadvertently contains a comment ending in Coq. Therefore, we will add a special character to remove any comment start or end non-code. The above sentence will become `(Water *proof*💧) text`.

## String literals

Moreover, Coq string literals in comments *must* be completed in order to be parsed correctly. Strings begin and end with double quotes (`"`). Hence, to avoid an odd number of double quotes, we duplicate every occurence of `"`.

## Notebook or exercise sheet?

Currently always import as notebook. So previously exported exercise sheet can become notebook. Should this be different?

## Summary

For every waterproof block, which is an object that looks like `{type: String, ?text: String, ?start: Boolean, ?id: String}`, the Coq equivalent will be: 
- `(*💧type: [type]*)\n[text]` if type is `code`.
- `(*💧type: [type], start: [start], id: [id]*)` if type is `input`.
- `(*💧type: [type]*)\n(*[text]*)` for other types.

We separate blocks by adding an extra newline.

Moreover, for non code blocks, all text in `text` is filtered to replace `(*` and `*)` with `(💧*` and `*💧)` respectively, and double quotes (`"`) are duplicated.

The inverse is done to import.