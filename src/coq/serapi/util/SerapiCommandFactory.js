import {sanitise} from '../SerapiParser';

/**
 * Create a serapi add command
 * @param {String} content the content to be added
 * @return {string} the command
 */
export function createAddCommand(content) {
  return `(Add () "${sanitise(content)}")`;
}

/**
 * Create a serapi cancel command
 * @param {String} sentences the sentences to cancel
 * @return {string} the command
 */
export function createCancelCommand(sentences) {
  return `(Cancel (${sentences.join(' ')}))`;
}

/**
 * Create a serapi execute command
 * @param {String} sentenceId the sentence to be executed
 * @return {string} the command
 */
export function createExecuteCommand(sentenceId) {
  return `(Exec ${sentenceId})`;
}

/**
 * Partial method for query commands
 * @param {String} sentenceId the sentence to query
 * @param {String} format the format to use
 * @param {String} command the command to use
 * @return {String} the command
 * @private
 */
function querySentenceCommand(sentenceId, format, command) {
  return `(Query ((sid ${sentenceId})(pp ((pp_format ${format})))) ${command})`;
}

/**
 * Create a serapi goal command
 * @param {String} sentenceId the sentence to get the goal from
 * @param {String} format the format to use
 * @return {string} the command
 */
export function createGoalCommand(sentenceId, format = 'PpStr') {
  return querySentenceCommand(sentenceId, format, 'Goals');
}

/**
 * Create a serapi ast command
 * @param {String} sentenceId the sentence to get the ast from
 * @param {String} format the format to use
 * @return {string} the command
 */
export function createASTCommand(sentenceId, format = 'PpSer') {
  return querySentenceCommand(sentenceId, format, 'Ast');
}

/**
 * Partial method for vernac commands
 * @param {String} command the vernac commmand to execute
 * @return {string} the command
 */
export function createQueryVernacCommand(command) {
  return `(Query () (Vernac "${sanitise(command)}"))`;
}

/**
 * Partial method for vernac commands to execute the command
 * after a specific sentece
 * @param {String} command the vernac commmand to execute
 * @param {number} sentenceId the sentence id after which
 * the command should execute
 * @return {string} the command
 */
export function createIndexedQueryVernacCommand(command, sentenceId) {
  return `(Query ((sid ${sentenceId})) (Vernac "${sanitise(command)}"))`;
}

/**
 * Create a serapi check command
 * @param {String} query the term to check for
 * @return {string} the command
 */
export function createCheckCommand(query) {
  return createQueryVernacCommand(`Check (${query}).`);
}

/**
 * Create a serapi search command
 * @param {String} query the term to check for
 * @return {string} the command
 */
export function createSearchCommand(query) {
  return createQueryVernacCommand(`Search ${query}.`);
}
