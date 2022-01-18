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
        let find_file = |offset: usize| {
            let i = self.files.partition_point(|f| f.offset <= offset);
            &self.files[i - 1]
        };
        let from_file = find_file(p.begin);
        let to_file = find_file(p.end);
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

#[derive(Debug)]
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
