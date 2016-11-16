Mutable closures work out of the box as long as they don't close over mutable references - that would require [nested storing of `&mut`](#nested-storing-of-mut-refs.).
