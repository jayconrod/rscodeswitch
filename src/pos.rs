use std::cmp::PartialOrd;
use std::fmt::{self, Display, Formatter};
use std::path::{Path, PathBuf};

/// LineMap translates raw byte offsets (Pos) into human-readable file
/// locations (Position). This works by keeping an index of byte offsets
/// of each line in each file passed to the lexer.
pub struct LineMap {
    files: Vec<File>,
    base: usize,
}

struct File {
    offset: usize,
    path: PathBuf,
    lines: Vec<usize>,
}

impl LineMap {
    /// Creates a new, empty LineMap. add_file, then add_line must be called
    /// before translating positions.
    pub fn new() -> LineMap {
        LineMap {
            files: Vec::<File>::new(),
            base: 0,
        }
    }

    /// Adds a file with the given name and size to the line map.
    ///
    /// add_file returns the base offset of this file. Pos values may be
    /// constructed by adding this base offset to an offset within the file.
    ///
    /// After calling add_file, add_line may be called with the offset of
    /// the beginning of each line, in order, not including the first line.
    pub fn add_file(&mut self, filename: &Path, size: usize) -> usize {
        let base = self.base;
        self.files.push(File {
            offset: base,
            path: PathBuf::from(filename),
            lines: Vec::new(),
        });
        self.base += size;
        self.add_line(0);
        base
    }

    /// Adds the offset of the beginning of a line within the
    /// current file (from the most recent call to add_file).
    pub fn add_line(&mut self, offset: usize) {
        let file = self.files.last_mut().unwrap();
        assert!(file.lines.last().map(|&l| l < offset).unwrap_or(true));
        file.lines.push(offset);
    }

    /// Expands a Pos (which only contains offsets in a LineMap) into a
    /// human-readable Position. Position takes more space, so this should only
    /// be done when needed.
    pub fn position(&self, p: Pos) -> Position {
        let from_file = &self.files[self.find_file_index(p.begin)];
        let to_file = &self.files[self.find_file_index(p.end)];
        assert!(from_file.offset == to_file.offset);

        let find_line_and_col = |offset: usize| {
            let line = from_file.lines.partition_point(|&l| l <= offset) - 1;
            let col = offset - from_file.lines[line];
            (line + 1, col + 1) // Count from 1, not 0.
        };
        let (begin_line, begin_col) = find_line_and_col(p.begin);
        let (end_line, end_col) = find_line_and_col(p.end);
        Position {
            path: from_file.path.clone(),
            begin_line,
            begin_col,
            end_line,
            end_col,
        }
    }

    pub fn first_file(&self) -> Position {
        let path = match self.files.first() {
            Some(f) => f.path.clone(),
            None => PathBuf::from(""),
        };
        Position {
            path,
            begin_line: 0,
            begin_col: 0,
            end_line: 0,
            end_col: 0,
        }
    }

    /// Encodes the file and line number for a given position. Encoded lines
    /// are saved in compiled functions for use in error messages and
    /// stack traces.
    pub fn encode_line(&self, pos: Pos) -> EncodedLine {
        // TODO: handle overflow when the number of lines doesn't fit into u32.
        // For now, panic.
        let offset = pos.begin;
        let i = self.find_file_index(offset);
        let base: usize = self.files[..i].iter().map(|f| f.lines.len()).sum();
        let offset_in_file = offset - self.files[i].offset;
        let line: usize = self.files[i]
            .lines
            .partition_point(|&l| l <= offset_in_file)
            - 1;
        let enc: u32 = (base + line).try_into().unwrap();
        EncodedLine(enc)
    }

    fn find_file_index(&self, offset: usize) -> usize {
        let i = self.files.partition_point(|f| f.offset <= offset);
        i - 1
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Pos {
    pub begin: usize,
    pub end: usize,
}

impl Pos {
    pub fn combine(self, other: Pos) -> Pos {
        Pos {
            begin: self.begin,
            end: other.end,
        }
    }
}

impl Default for Pos {
    fn default() -> Pos {
        Pos { begin: 0, end: 0 }
    }
}

/// An encoded file and line number, used with PackageLineMap and
/// FunctionLineMap. The value is the sum of lines in the files before
/// the indicated file in PackageLineMap, plus the 0-based line number.
///
/// For example, if PackageLineMap contains three files:
///
/// - foo.rs: 100 lines
/// - bar.rs: 200 lines
/// - baz.rs: 300 lines
///
/// Then the encoded value 150 would be bar.rs, line 50.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct EncodedLine(u32);

const INVALID_ENCODED_LINE: EncodedLine = EncodedLine(!0);

/// PackageLineMap is a list of the source file names used to build the
/// package, and the number of lines in each file. PackageLineMap is used
/// to transform an instruction offset within a function into a file name
/// and line number, for use in error messages and stack traces.
pub struct PackageLineMap {
    pub files: Vec<FileLineCount>,
}

impl PackageLineMap {
    /// Transforms an instruction offset within a function into a Position
    /// with the file name and line number, using the function's line map.
    /// If the position can't be found, for example, because the function
    /// has no line number information, Position::unknown() is returned.
    pub fn position(&self, offset: u32, flmap: &FunctionLineMap) -> Position {
        let encoded_line = flmap.lookup(offset);
        if encoded_line == INVALID_ENCODED_LINE {
            return Position::default();
        }
        let mut enc = encoded_line.0;
        for f in &self.files {
            if enc < f.line_count {
                return Position {
                    path: f.path.clone(),
                    begin_line: enc as usize + 1,
                    begin_col: 0,
                    end_line: enc as usize + 1,
                    end_col: 0,
                };
            }
            enc -= f.line_count;
        }
        Position::default()
    }
}

impl From<&LineMap> for PackageLineMap {
    /// Builds a PackageLineMap from the LineMap used when parsing the package's
    /// sources. This is convenient since a bytecode compiler may use
    /// LineMap::encode_line while building FunctionLineMaps.
    fn from(lmap: &LineMap) -> PackageLineMap {
        PackageLineMap {
            files: lmap
                .files
                .iter()
                .map(|f| FileLineCount {
                    path: f.path.clone(),
                    line_count: f.lines.len().try_into().unwrap_or(u32::MAX),
                })
                .collect(),
        }
    }
}

pub struct FileLineCount {
    pub path: PathBuf,
    pub line_count: u32,
}

/// Contains a table of (instruction offset, encoded line) pairs. The
/// representation is encoded to limit its size. This makes finding a particular
/// entry slower, but it saves quite a bit of space.
///
/// Use FunctionLineMapBuilder to construct a new map.
pub struct FunctionLineMap {
    data: Vec<u8>,
}

impl FunctionLineMap {
    pub fn new() -> FunctionLineMap {
        FunctionLineMap { data: Vec::new() }
    }

    /// Given an instruction offset, lookup finds the entry with the highest
    /// instruction offset less than or equal to the given offset, then returns
    /// the encoded line from that entry. If there is no such entry, for
    /// example because the table is empty, lookup returns INVALID_ENCODED_LINE.
    pub fn lookup(&self, offset: u32) -> EncodedLine {
        // data consists of a list of "commands" that create entries.
        //
        // The low seven bits of the first byte of a command are an offset
        // added to the previous entry's instruction offset (or 0 if there was
        // no previous entry).
        //
        // If the high bit of the command's first byte is clear, that's the
        // complete offset. Otherwise, there is at least one more offset byte
        // encoded the same way.
        //
        // The next four bytes are an encoded line in little-endian order.

        let mut p = 0;
        let mut prev_offset = 0;
        let mut cmd_offset = 0;
        let mut prev_line = INVALID_ENCODED_LINE;
        while p < self.data.len() {
            let c = self.data[p];
            if c & 0x80 != 0 {
                cmd_offset += (c & 0x7f) as u32;
                p += 1;
                continue;
            }
            cmd_offset += c as u32;
            if prev_offset <= offset && offset < cmd_offset {
                return prev_line;
            }
            prev_offset = cmd_offset;
            if p + 5 > self.data.len() {
                // Reached the end of the data, even though we expect to find
                // a line after each command. This indicates the data is
                // corrupted or incomplete. This isn't a hard failure though.
                return INVALID_ENCODED_LINE;
            }
            prev_line = EncodedLine(u32::from_le_bytes(
                self.data[p + 1..p + 5].try_into().unwrap(),
            ));
            p += 5;
        }
        prev_line
    }
}

pub struct FunctionLineMapBuilder {
    data: Vec<u8>,
    prev_inst_offset: u32,
    prev_encoded_line: EncodedLine,
}

impl FunctionLineMapBuilder {
    pub fn new() -> FunctionLineMapBuilder {
        FunctionLineMapBuilder {
            data: Vec::new(),
            prev_inst_offset: 0,
            prev_encoded_line: INVALID_ENCODED_LINE,
        }
    }

    pub fn build(self) -> FunctionLineMap {
        FunctionLineMap { data: self.data }
    }

    pub fn add_line(&mut self, inst_offset: usize, encoded_line: EncodedLine) {
        if !self.data.is_empty() && self.prev_encoded_line == encoded_line {
            // Previous entry points to the same line.
            // No need to add a new entry.
            return;
        }
        let inst_offset: u32 = inst_offset.try_into().unwrap();
        let mut delta = inst_offset - self.prev_inst_offset;
        while delta > 0x7f {
            self.data.push(0xff);
            delta -= 0x7f;
        }
        self.data.push(delta as u8);
        self.data.extend_from_slice(&encoded_line.0.to_le_bytes());
        self.prev_inst_offset = inst_offset;
        self.prev_encoded_line = encoded_line;
    }
}

#[derive(Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Position {
    pub path: PathBuf,
    pub begin_line: usize,
    pub begin_col: usize,
    pub end_line: usize,
    pub end_col: usize,
}

impl From<&str> for Position {
    fn from(path: &str) -> Position {
        Position::from(PathBuf::from(path).as_path())
    }
}

impl From<&Path> for Position {
    fn from(path: &Path) -> Position {
        Position {
            path: PathBuf::from(path),
            begin_line: 0,
            begin_col: 0,
            end_line: 0,
            end_col: 0,
        }
    }
}

impl Default for Position {
    fn default() -> Position {
        Position {
            path: PathBuf::from("<unknown>"),
            begin_line: 0,
            begin_col: 0,
            end_line: 0,
            end_col: 0,
        }
    }
}

impl Display for Position {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let path = self.path.to_string_lossy();
        if self.begin_line == 0 {
            write!(f, "{}", path)
        } else if self.begin_col == 0 {
            if self.begin_line == self.end_line {
                write!(f, "{}:{}", path, self.begin_line)
            } else {
                write!(f, "{}:{}-{}", path, self.begin_line, self.end_line)
            }
        } else {
            if self.begin_line == self.end_line && self.begin_col == self.end_col {
                write!(f, "{}:{}.{}", path, self.begin_line, self.begin_col)
            } else {
                write!(
                    f,
                    "{}:{}.{}-{}.{}",
                    path, self.begin_line, self.begin_col, self.end_line, self.end_col
                )
            }
        }
    }
}

#[derive(Debug)]
pub struct Error {
    pub position: Position,
    pub message: String,
}

impl Error {
    pub fn new(position: Position, message: &str) -> Error {
        Error {
            position,
            message: String::from(message),
        }
    }

    pub fn wrap(position: Position, err: &dyn Display) -> Error {
        let message = format!("{}", err);
        Error { position, message }
    }
}

impl Display for Error {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}: {}", self.position, self.message)
    }
}

impl std::error::Error for Error {}

#[derive(Debug)]
pub struct ErrorList(pub Vec<Error>);

impl ErrorList {
    pub fn new(position: Position, message: &str) -> ErrorList {
        ErrorList::from(Error::new(position, message))
    }

    pub fn wrap(position: Position, err: &dyn Display) -> ErrorList {
        ErrorList::from(Error::wrap(position, err))
    }
}

impl From<Error> for ErrorList {
    fn from(err: Error) -> ErrorList {
        ErrorList(vec![err])
    }
}

impl From<Vec<Error>> for ErrorList {
    fn from(mut errs: Vec<Error>) -> ErrorList {
        errs.sort_by(|l, r| l.position.cmp(&r.position));
        ErrorList(errs)
    }
}

impl Display for ErrorList {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let mut sep = "";
        for err in &self.0 {
            write!(f, "{}{}", sep, err)?;
            sep = "\n";
        }
        Ok(())
    }
}

impl std::error::Error for ErrorList {}
