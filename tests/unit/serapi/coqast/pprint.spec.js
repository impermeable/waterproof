const chai = require('chai');
const {default: CoqType} =
  require('../../../../src/coq/serapi/datastructures/CoqType');
const expect = chai.expect;
const suppressLogs = require('mocha-suppress-logs');
const { default: GenericVType } = require('../../../../src/coq/serapi/datastructures/GenericVType');
const { default: VernacExtend } = require('../../../../src/coq/serapi/datastructures/VernacExtend');


describe('Pretty-printer', ()=> {
  suppressLogs();

  describe('helper functions', () => {
    suppressLogs();

    it('sprinf with 0 inputs', (done) => {
      const t = new CoqType([]);
      const str = 'Hi %s';
      expect(t.sprintf(str)).to.equal(str);
      done();
    });
    it('sprinf with 2 inputs', (done) => {
      const t = new CoqType([]);
      const str = 'Hi %s!%s';
      expect(t.sprintf(str, 'Sam')).to.equal('Hi Sam!%s');
      expect(t.sprintf(str, 'Sam', '\nGood morning.'))
          .to.equal('Hi Sam!\nGood morning.');
      done();
    });
    it('sprintf with n inputs', (done) => {
      const t = new CoqType([]);
      let str = '%s '.repeat(10);
      for (let i = 0; i < 10; i++) {
        str = t.sprintf(str, i);
      }
      expect(str).to.equal('0 1 2 3 4 5 6 7 8 9 ');
      done();
    });
    it('cprint with array', (done) => {
      const t = new CoqType([]);
      console.log(t.cprint([1, 2, 3]));
      expect(t.cprint([1, 2, 3], -1)).to.equal('Content: \n\t1,2,3\n');
      done();
    });
    it('cprint with object', (done) => {
      const t = new CoqType([]);
      const v = new VernacExtend(['VernacExtend', '', '']);
      console.log(t.cprint([1, 2, 3]));
      expect(t.cprint(v, -1)).to.equal('Content: \n'+v.data);
      done();
    });
  });
});
