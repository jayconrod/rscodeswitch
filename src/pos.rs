use std::fmt;

pub struct LineMap {
    files: Vec<File>,
    base: usize,
}

struct File {
    offset: usize,
    filename: String,
    lines: Vec<usize>,
}

impl LineMap {
    pub fn new() -> LineMap {
        LineMap {
            files: Vec::<File>::new(),
            base: 0,
        }
    }

    pub fn add_file(&mut self, filename: &str, size: usize) -> usize {
        let base = self.base;
        self.files.push(File {
            offset: base,
            filename: String::from(filename),
            lines: Vec::new(),
        });
        self.base += size;
        base
    }

    pub fn add_line(&mut self, offset: usize) {
        let file = self.files.last_mut().unwrap();
        assert!(file.lines.last().map(|&l| l < offset).unwrap_or(true));
        file.lines.push(offset);
    }

    pub fn position(&self, from: Pos, to: Pos) -> Position {
        let find_file = |pos: Pos| {
            let i = self.files.partition_point(|f| f.offset <= pos.offset);
            &self.files[i - 1]
        };
        let from_file = find_file(from);
        let to_file = find_file(to);
        assert!(from_file.offset == to_file.offset);

        let find_line_and_col = |pos: Pos| {
            let line = from_file.lines.partition_point(|&l| l <= pos.offset);
            let col = pos.offset - from_file.lines[line - 1];
            (line + 1, col + 1) // Count from 1, not 0.
        };
        let (from_line, from_col) = find_line_and_col(from);
        let (to_line, to_col) = find_line_and_col(to);
        Position {
            filename: from_file.filename.clone(),
            from_line,
            from_col,
            to_line,
            to_col,
        }
    }

    pub fn first_file(&self) -> Position {
        let filename = match self.files.first() {
            Some(f) => f.filename.clone(),
            None => String::from(""),
        };
        Position {
            filename,
            from_line: 0,
            from_col: 0,
            to_line: 0,
            to_col: 0,
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Pos {
    pub offset: usize,
}

#[derive(Debug)]
pub struct Position {
    pub filename: String,
    pub from_line: usize,
    pub from_col: usize,
    pub to_line: usize,
    pub to_col: usize,
}

impl fmt::Display for Position {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.from_line == 0 {
            write!(f, "{}", self.filename)
        } else if self.from_col == 0 {
            if self.from_line == self.to_line {
                write!(f, "{}:{}", self.filename, self.from_line)
            } else {
                write!(f, "{}:{}-{}", self.filename, self.from_line, self.to_line)
            }
        } else {
            if self.from_line == self.to_line && self.from_col == self.to_col {
                write!(f, "{}:{}.{}", self.filename, self.from_line, self.from_col)
            } else {
                write!(
                    f,
                    "{}:{}.{}-{}.{}",
                    self.filename, self.from_line, self.from_col, self.to_line, self.to_col
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
    pub fn wrap(position: Position, err: &dyn std::error::Error) -> Error {
        let message = format!("{}", err);
        Error { position, message }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.position, self.message)
    }
}

impl std::error::Error for Error {}
