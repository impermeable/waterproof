import CodeMirror from 'codemirror';

CodeMirror.defineMode('coq', function(_config, _parserConfig) {
  /* eslint-disable */
  const vernacular = [
    'Abort', 'About', 'Add', 'All', 'Arguments', 'Asymmetric', 'Axiom',
    'Bind',
    'Canonical', 'Check', 'Class', 'Close', 'Coercion', 'CoFixpoint', 'Comments',
    'CoInductive', 'Compute', 'Context', 'Constructors', 'Contextual', 'Corollary',
    'Defined', 'Definition', 'Delimit',
    'Fail',
    'Eval',
    'End', 'Example', 'Export',
    'Fact', 'Fixpoint', 'From',
    'Global', 'Goal', 'Graph',
    'Hint', 'Hypotheses', 'Hypothesis',
    'Implicit', 'Implicits', 'Import', 'Inductive', 'Infix', 'Instance',
    'Lemma', 'Let', 'Local', 'Ltac',
    'Module', 'Morphism',
    'Next', 'Notation',
    'Obligation', 'Open',
    'Parameter', 'Parameters', 'Prenex', 'Print', 'Printing', 'Program',
    'Patterns', 'Projections', 'Proof',
    'Proposition',
    'Qed',
    'Record', 'Relation', 'Remark', 'Require', 'Reserved', 'Resolve', 'Rewrite',
    'Save', 'Scope', 'Search', 'SearchAbout', 'Section', 'Set', 'Show', 'Strict', 'Structure',
    'Tactic', 'Time', 'Theorem', 'Types',
    'Unset',
    'Variable', 'Variables', 'View',
  ];

  const gallina = [
    'as',
    'at',
    'cofix', 'crush',
    'else', 'end',
    'False', 'fix', 'for', 'forall', 'fun',
    'if', 'in', 'is',
    'let',
    'match',
    'of',
    'Prop',
    'return',
    'struct',
    'then', 'True', 'Type',
    'when', 'with',
  ];

  const tactics = [
    'after', 'apply', 'assert', 'auto', 'autorewrite',
    'case', 'change', 'clear', 'compute', 'congruence', 'constructor',
    'congr', 'cut', 'cutrewrite',
    'dependent', 'destruct',
    'eapply', 'eassumption', 'eauto', 'econstructor', 'elim', 'exists',
    'field', 'firstorder', 'fold', 'fourier',
    'generalize',
    'have', 'hnf',
    'induction', 'injection', 'instantiate', 'intro', 'intros', 'inversion',
    'left',
    'move',
    'pattern', 'pose',
    'refine', 'remember', 'rename', 'repeat', 'replace', 'revert', 'rewrite',
    'right', 'ring',
    'set', 'simpl', 'specialize', 'split', 'subst', 'suff', 'symmetry',
    'transitivity', 'trivial', 'try',
    'unfold', 'unlock', 'using',
    'vm_compute',
    'where', 'wlog',
  ];

  const terminators = [
    'assumption',
    'by',
    'contradiction',
    'discriminate',
    'easy',
    'exact',
    'now',
    'omega',
    'reflexivity',
    'tauto',
  ];

  const admitters = [
    'admit',
    'Admitted',
  ];

  const lexOperators =
      /=>|:=|<:|<<:|:>|->|<->?|\\\/|\/\\|>=|<=|<>|\+\+|::|\|\||&&|\.\./;

  const lexBrackets = /\.\(|\{\||\|\}|`\{|`\(/;

  // Map assigning each keyword a category.
  const words = {};

  // We map
  // - gallina keywords -> CM keywords
  // - vernaculars      -> CM builtins
  // - admitters        -> CM keywords XXX
  gallina .map(function(word) {
    words[word] = 'keyword';
  });
  admitters .map(function(word) {
    words[word] = 'keyword';
  });
  vernacular .map(function(word) {
    words[word] = 'builtin';
  });

  tactics .map(function(word) {
    words[word] = 'tactic';
  });
  terminators.map(function(word) {
    words[word] = 'terminator';
  });

  /*
    Coq mode defines the following state variables:
    - begin_sentence: only \s caracters seen from the last sentence.
    - is_head: at first (non-comment, non-space) token of sentence.
    - sentence_kind: kind of the head token.
    - commentLevel [:int] = Level of nested comments.
    - tokenize [:func] = current active tokenizer. We provide 4 main ones:
      + tokenBase: Main parser, it reads the next character and
        setups the next tokenizer. In particular it takes care of
        braces. It doesn't properly analyze the sentences and
        bracketing.
      + tokenStatementEnd: Called when a dot is found in tokenBase,
        it looks ahead on the string and returns statement end.
      + tokenString: Takes care of escaping.
      + tokenComment: Takes care of nested comments.
   */

  /*
    Codemirror lexing functions:
    - eat(s) = eat next char if s
    - eatWhile(s) = eat s until fails
    - match(regexp) => return array of matches and optionally eat
   */
  function tokenBase(stream, state) {
    const at_sentence_start = state.begin_sentence;

    state.is_head = false;

    // If any space in the input, return null.
    if (stream.eatSpace()) {
      return null;
    }

    if (stream.match(lexOperators)) return 'operator';

    // if (stream.match(lex_brackets))  return 'bracket';
    // ^ skipped, for the time being, because matchbracket does not support
    //   multi-character brackets.

    const ch = stream.next();

    if (at_sentence_start && (/[-*+{}]/.test(ch))) {
      return 'coq-bullet';
    }

    // Preserve begin sentence after comment.
    if (ch === '(') {
      if (stream.peek() === '*') {
        stream.next();
        state.commentLevel++;
        state.tokenize = tokenComment;
        return state.tokenize(stream, state);
      }
      state.begin_sentence = false;
      return 'parenthesis';
    }

    if ( ! (/\s/.test(ch)) ) {
      state.begin_sentence = false;
    }

    if (ch === '.') {
      state.tokenize = tokenStatementEnd;
      return state.tokenize(stream, state);
    }

    if (ch === '"') {
      state.tokenize = tokenString;
      return state.tokenize(stream, state);
    }

    if (ch === ')') {
      return 'parenthesis';
    }

    if (/\d/.test(ch)) {
      stream.eatWhile(/[\d]/);
      /*
      if (stream.eat('.')) {
        stream.eatWhile(/[\d]/);
      }
      */
      return 'number';
    }

    if ( /[+\-*&%=<>!?|,;:\^#@~`]/.test(ch)) {
      return 'operator';
    }

    if (/[\[\]]/.test(ch)) {
      return 'bracket';
    }

    /* Identifier or keyword*/
    if (/\w/.test(ch)) {
      stream.eatWhile(/[\w']/);
    }

    const cur = stream.current();
    const kind = words[cur] || 'variable';

    if (at_sentence_start) {
      state.sentence_kind = kind;
      state.is_head = true;
    }

    return kind;
  }

  function tokenString(stream, state) {
    let next; let end = false; let escaped = false;
    while ((next = stream.next()) != null) {
      if (next === '"' && !escaped) {
        end = true;
        break;
      }
      escaped = !escaped && next === '\\';
    }
    if (end && !escaped) {
      state.tokenize = tokenBase;
    }
    return 'string';
  }

  function tokenComment(stream, state) {
    let ch;
    while (state.commentLevel && (ch = stream.next())) {
      if (ch === '(' && stream.peek() === '*') {
        stream.next();
        state.commentLevel++;
      }

      if (ch === '*' && stream.peek() === ')') {
        stream.next();
        state.commentLevel--;
      }
    }

    if (!state.commentLevel) {
      state.tokenize = tokenBase;
    }

    return 'comment';
  }

  function tokenStatementEnd(stream, state) {
    state.tokenize = tokenBase;

    if (stream.eol() || stream.match(/\s/, false)) {
      state.begin_sentence = true;
      state.sentence_kind = undefined;
      return 'statementend';
    }
  }

  return {
    startState: function() {
      return {begin_sentence: true, is_head: false, tokenize: tokenBase, commentLevel: 0};
    },

    token: function(stream, state) {
      return state.tokenize(stream, state);
    },

    blockCommentStart: '(*',
    blockCommentEnd: '*)',
    lineComment: null,
  };
});

CodeMirror.defineMIME('text/x-coq', {
  name: 'coq',
});
