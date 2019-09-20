import {sanitise} from '../SerapiParser';

export function createAddCommand(content) {
  return `(Add () "${sanitise(content)}"`;
}

export function createCancelCommand(sentences) {
  return `(Cancel (${sentences.join(' ')}))`;
}

export function createExecuteCommand(sentenceId) {
  return `(Exec ${sentenceId})`;
}

function querySentenceCommand(sentenceId, format, command) {
  return `(Query ((sid ${sentenceId})(pp ((pp_format ${format})))) ${command}`;
}

export function createGoalCommand(sentenceId, format = 'PpStr') {
  return querySentenceCommand(sentenceId, format, 'Goals');
}

export function createASTCommand(sentenceId, format = 'PpSer') {
  return querySentenceCommand(sentenceId, format, 'Ast');
}

export function createQueryVernacCommand(command) {
  return `(Query () (Vernac "${sanitise(command)}"))`;
}

export function createCheckCommand(query) {
  return createQueryVernacCommand(`Check (${query}).`);
}

export function createSearchCommand(query) {
  return createQueryVernacCommand(`Search ${query}.`);
}
