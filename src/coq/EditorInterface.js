'use strict';


/**
 * Callbacks for the editor side
 */
class EditorInterface {
  /**
   * Interface for editor
   */
  constructor() {
  }


  /**
   * Called when setContent was completed without error
   * @param {String|null} goal if goal should be updated goal != null
   * @param {Number} index the index to where execution is still valid
   * @param {boolean} removeAddError  Whether the current addError is removed
   */
  setContentSuccess(goal, index, removeAddError) {
  }


  /**
   * Called when setContent ran into an error
   * (But some sentences might have been added)
   * @param {String} error the error that occurred
   * @param {Number} errorIndex the first index where the error occurred
   */
  setContentError(error, errorIndex) {
  }

  /**
   * Called when execution is requested
   * @param {Number} index the index to where execution will go
   */
  executeStarted(index) {
  }

  /**
   * When any execute is successful
   *   next, prev, to
   * @param {String} goal if goal should be updated goal != null
   * @param {Number} index the index to where execution is still valid
   * @param {Boolean} proofFinished true when Qed. is executed successfully
   */
  executeSuccess(goal, index, proofFinished) {
  }

  /**
   * When any execution has an error
   * @param {String} error the error that occurred
   * @param {{start, end}} errorIndex the first index where the error occurred
   */
  executeError(error, errorIndex) {
  }

  /**
   * When coq gives some message
   * @param {String} message the message
   * @param {Number} sentenceId the id of the sentence or null
   */
  message(message, sentenceId=null) {
  }

  /**
   * Called whenever the coq instance is ready to receive messages
   */
  onReady() {
  }
}

export default EditorInterface;
