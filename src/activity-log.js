const ipcRenderer = (() => {
  if (process.env.NODE_ENV === 'test') {
    return {
      send(channel, activity) {
        console.log('Would have written', activity, 'to', channel);
      },
    };
  } else {
    return require('electron').ipcRenderer;
  }
})();

export function writeActivity(type, details = {}) {
  ipcRenderer.send('activity', Object.assign({type}, details));
}
