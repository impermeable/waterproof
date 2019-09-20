import Recents from '../../../src/io/recents';

const chai = require('chai');
const expect = chai.expect;

const recents = new Recents;
recents.allowWriting = false;

describe('The recent file list', () => {
  beforeEach(() => {
    recents.allowWriting = false;
    recents.clearRecentFileList();
  });

  const fileUnixPathOne = `C:/root/folder/FolderTwo/ThirdFolder/filename.wpn`;
  const fileUnixPathTwo = `C:/root/folder/FolderTwo/ThirdFolder/exercise.wpn`;
  const fileUnixPathThree = `C:/root/folder/SomeFolder/AFolder/filenameX.wpn`;

  const fileWindowsPathOne =
          `C:\\Users\\someUser\\Documents\\Folder\\filename.wpn`;
  const fileWindowsPathTwo =
          `C:\\Users\\someUser\\Documents\\Folder\\Folder2\\filename.wpn`;
  const fileWindowsPathThree =
          `C:\\Users\\someUser\\Downloads\\exerciseSheet9.wpn`;

  describe('addFileListEntry', () => {
    it('should add file with unix path', (done) => {
      expect(recents.filelist.length).to.equal(0);
      recents.addFileListEntry(fileUnixPathOne);
      expect(recents.filelist.length).to.equal(1);
      expect(recents.filelist[0].location).to.equal(fileUnixPathOne);
      done();
    });

    it('should add file with windows path', (done) => {
      expect(recents.filelist.length).to.equal(0);
      recents.addFileListEntry(fileWindowsPathOne);
      expect(recents.filelist.length).to.equal(1);
      expect(recents.filelist[0].location).to.equal(fileWindowsPathOne);
      done();
    });

    it('should add already existing entry with unix path ', (done) => {
      expect(recents.filelist.length).to.equal(0);
      recents.addFileListEntry(fileUnixPathOne);
      expect(recents.filelist.length).to.equal(1);
      expect(recents.filelist[0].location).to.equal(fileUnixPathOne);
      recents.addFileListEntry(fileUnixPathOne);
      expect(recents.filelist.length).to.equal(1);
      expect(recents.filelist[0].location).to.equal(fileUnixPathOne);
      done();
    });

    it('should add already existing entry with windows path ', (done) => {
      expect(recents.filelist.length).to.equal(0);
      recents.addFileListEntry(fileWindowsPathOne);
      recents.addFileListEntry(fileWindowsPathOne);
      expect(recents.filelist.length).to.equal(1);
      expect(recents.filelist[0].location).to.equal(fileWindowsPathOne);
      done();
    });

    it('should not add the Tutorial entry', (done) => {
      expect(recents.filelist.length).to.equal(0);
      recents.addFileListEntry('Tutorial');
      expect(recents.filelist.length).to.equal(0);
      done();
    });

    it('should add multiple entries with unix path ', (done) => {
      expect(recents.filelist.length).to.equal(0);
      recents.addFileListEntry(fileUnixPathOne);
      recents.addFileListEntry(fileUnixPathTwo);
      recents.addFileListEntry(fileUnixPathThree);
      expect(recents.filelist.length).to.equal(3);
      expect(recents.filelist[0].location).to.equal(fileUnixPathThree);
      expect(recents.filelist[1].location).to.equal(fileUnixPathTwo);
      expect(recents.filelist[2].location).to.equal(fileUnixPathOne);
      done();
    });

    it('should add multiple entries with windows path ', (done) => {
      expect(recents.filelist.length).to.equal(0);
      recents.addFileListEntry(fileWindowsPathOne);
      recents.addFileListEntry(fileWindowsPathTwo);
      recents.addFileListEntry(fileWindowsPathThree);
      expect(recents.filelist.length).to.equal(3);
      expect(recents.filelist[0].location).to.equal(fileWindowsPathThree);
      expect(recents.filelist[1].location).to.equal(fileWindowsPathTwo);
      expect(recents.filelist[2].location).to.equal(fileWindowsPathOne);
      done();
    });

    it('should adjust order after inserting entries with unix path ',
        (done) => {
          expect(recents.filelist.length).to.equal(0);
          recents.addFileListEntry(fileUnixPathOne);
          recents.addFileListEntry(fileUnixPathTwo);
          recents.addFileListEntry(fileUnixPathOne);
          expect(recents.filelist.length).to.equal(2);
          expect(recents.filelist[0].location).to.equal(fileUnixPathOne);
          expect(recents.filelist[1].location).to.equal(fileUnixPathTwo);
          done();
        }
    );

    it('should adjust order after inserting entry with windows path ',
        (done) => {
          expect(recents.filelist.length).to.equal(0);
          recents.addFileListEntry(fileWindowsPathOne);
          recents.addFileListEntry(fileWindowsPathTwo);
          recents.addFileListEntry(fileWindowsPathOne);
          expect(recents.filelist.length).to.equal(2);
          expect(recents.filelist[0].location).to.equal(fileWindowsPathOne);
          expect(recents.filelist[1].location).to.equal(fileWindowsPathTwo);
          done();
        }
    );

    it('should keep at most maxLength entries in list for unix',
        (done) => {
          recents.addFileListEntry(fileUnixPathOne);
          let location;
          for (let i = 0; i < recents.maxFileListLength - 2; i++) {
            location = 'C:/root/file' + i + '.wpn';
            recents.addFileListEntry(location);
          }
          expect(recents.filelist.length).to.equal(recents.maxFileListLength-1);
          recents.addFileListEntry(fileUnixPathTwo);
          recents.addFileListEntry(fileUnixPathThree);
          expect(recents.filelist.length).to.equal(recents.maxFileListLength);
          expect(recents.filelist[0].location).to.equal(fileUnixPathThree);
          expect(recents.filelist[1].location).to.equal(fileUnixPathTwo);
          expect(recents.filelist[9].location).to.not.equal(fileUnixPathOne);
          done();
        }
    );

    it('should keep at most maxLength entries in list for windows',
        (done) => {
          recents.addFileListEntry(fileWindowsPathOne);
          let location;
          for (let i = 0; i < recents.maxFileListLength - 2; i++) {
            location = 'C:\\Users\\Name\\Documents\\Folder\\file' + i + '.wpn';
            recents.addFileListEntry(location);
          }
          recents.addFileListEntry(fileWindowsPathTwo);
          recents.addFileListEntry(fileWindowsPathThree);
          expect(recents.filelist.length).to.equal(recents.maxFileListLength);
          expect(recents.filelist[0].location).to.equal(fileWindowsPathThree);
          expect(recents.filelist[1].location).to.equal(fileWindowsPathTwo);
          expect(recents.filelist[9].location).to.not.equal(fileWindowsPathOne);
          done();
        }
    );
  });
});
