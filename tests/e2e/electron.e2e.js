const testWithSpectron =
  require('vue-cli-plugin-electron-builder/lib/testWithSpectron');
const chai = require('chai');
const chaiAsPromised = require('chai-as-promised');

chai.should();
chai.use(chaiAsPromised);

describe('Application launch', function() {
  // eslint-disable-next-line no-invalid-this
  this.timeout(60000);

  let app;
  let stopServe;

  beforeEach(function() {
    return testWithSpectron().then((instance) => {
      app = instance.app;
      stopServe = instance.stopServe;
    });
  });

  beforeEach(function() {
    chaiAsPromised.transferPromiseness = app.transferPromiseness;
  });

  afterEach(function() {
    if (app && app.isRunning()) {
      return stopServe();
    }
  });

  it('opens a window', function() {
    return app.client
        .getWindowCount()
        .should.eventually.be.equal(1)
        .browserWindow.isMinimized()
        .should.eventually.be.false.browserWindow.isVisible()
        .should.eventually.be.true.browserWindow.getBounds()
        .should.eventually.have.property('width')
        .and.be.above(0)
        .browserWindow.getBounds()
        .should.eventually.have.property('height')
        .and.be.above(0);
  });
});
