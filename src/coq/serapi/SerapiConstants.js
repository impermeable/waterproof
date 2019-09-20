const ADD_COMMAND = 'add';
const AST_COMMAND = 'ast';
const CANCEL_COMMAND = 'cancel';
const EXEC_COMMAND = 'exec';
const GOAL_COMMAND = 'goals';
const SEARCH_COMMAND = 'search';
const QUERY_COMMAND = 'query';
const CHECK_COMMAND = 'check';
const MESSAGE_COMPLETED = 'Completed';
const MESSAGE_ACK = 'Ack';
const COQ_EXCEPTION = 'CoqExn';
const MESSAGE_AFTER_READY = '(Feedback((doc_id 0)(span_id 1)' +
    '(route 0)(contents Processed)))';

export {
  ADD_COMMAND, AST_COMMAND, CANCEL_COMMAND,
  EXEC_COMMAND, GOAL_COMMAND, SEARCH_COMMAND,
  QUERY_COMMAND, CHECK_COMMAND, MESSAGE_COMPLETED, MESSAGE_ACK, COQ_EXCEPTION,
  MESSAGE_AFTER_READY,
};
