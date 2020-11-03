/**
 * A general interface for receiving messages and feedbacks from serapi
 * @interface
 */
class SerapiCallbacks {
  /**
   * Called when a message is received from serapi
   * @param {*} data the already parsed response from serapi
   * @param {String} extraTag the extra identifying tag
   */
  handleSerapiMessage(data, extraTag) {
  }
}

export default SerapiCallbacks;
