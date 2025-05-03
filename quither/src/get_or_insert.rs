// Copyright 2021 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use super::*;
use ::replace_with::replace_with_or_abort;
use quither_proc_macros::quither;

#[quither]
impl<L, R> Quither<L, R> {
    #[quither((!has_neither || has_either) && (!has_either || has_both))]
    pub fn insert_left(&mut self, #[allow(unused)] l: L) -> &mut L {
        match self {
            #[either]
            Self::Left(l) => l,
            #[either]
            Self::Right(_) => {
                replace_with_or_abort(self, move |this| {
                    let Self::Right(r) = this else { unreachable!() };
                    Self::Both(l, r)
                });
                let Self::Both(l, _) = self else {
                    unreachable!()
                };
                l
            }
            #[neither]
            Self::Neither => {
                replace_with_or_abort(self, move |_| Self::Left(l));
                let Self::Left(l) = self else { unreachable!() };
                l
            }
            #[both]
            Self::Both(l, _) => l,
        }
    }

    #[quither((!has_neither || has_either) && (!has_either || has_both))]
    pub fn insert_right(&mut self, #[allow(unused)] r: R) -> &mut R {
        match self {
            #[either]
            Self::Right(r) => r,
            #[either]
            Self::Left(_) => {
                replace_with_or_abort(self, move |this| {
                    let Self::Left(l) = this else { unreachable!() };
                    Self::Both(l, r)
                });
                let Self::Both(_, r) = self else {
                    unreachable!()
                };
                r
            }
            #[neither]
            Self::Neither => {
                replace_with_or_abort(self, move |_| Self::Right(r));
                let Self::Right(r) = self else { unreachable!() };
                r
            }
            #[both]
            Self::Both(_, r) => r,
        }
    }

    #[quither(has_both)]
    pub fn insert_both(
        &mut self,
        #[allow(unused)] l: L,
        #[allow(unused)] r: R,
    ) -> (&mut L, &mut R) {
        match self {
            #[either]
            Self::Left(_) => {
                replace_with_or_abort(self, move |this| {
                    let Self::Left(l) = this else { unreachable!() };
                    Self::Both(l, r)
                });
            }
            #[either]
            Self::Right(_) => {
                replace_with_or_abort(self, move |this| {
                    let Self::Right(r) = this else { unreachable!() };
                    Self::Both(l, r)
                });
            }
            #[neither]
            Self::Neither => {
                *self = Self::Both(l, r);
            }
            #[both]
            Self::Both(_, _) => (),
        };
        #[allow(irrefutable_let_patterns)]
        let Self::Both(l, r) = self else {
            unreachable!()
        };
        (l, r)
    }

    #[quither((!has_neither || has_either) && (!has_either || has_both))]
    pub fn left_or_insert(&mut self, l: L) -> &mut L {
        self.left_or_insert_with(move || l)
    }

    #[quither((!has_neither || has_either) && (!has_either || has_both))]
    pub fn right_or_insert(&mut self, r: R) -> &mut R {
        self.right_or_insert_with(move || r)
    }

    #[quither((!has_neither || has_either) && (!has_either || has_both))]
    pub fn left_or_insert_with<F>(&mut self, #[allow(unused)] f: F) -> &mut L
    where
        F: FnOnce() -> L,
    {
        match self {
            #[either]
            Self::Left(l) => l,
            #[either]
            Self::Right(_) => {
                // Right => Both promotion. It is guaranteed that the `Both` variant is present
                // because of the method's attribute.
                replace_with_or_abort(self, move |this| {
                    let Self::Right(r) = this else { unreachable!() };
                    Self::Both(f(), r)
                });
                let Self::Both(l, _) = self else {
                    unreachable!()
                };
                l
            }
            #[neither]
            Self::Neither => {
                // Neither => Left promotion. It is guaranteed that the `Left` variant is present
                // because of the method's attribute.
                replace_with_or_abort(self, move |this| {
                    let Self::Neither = this else { unreachable!() };
                    Self::Left(f())
                });
                let Self::Left(l) = self else { unreachable!() };
                l
            }
            #[both]
            Self::Both(l, _) => l,
        }
    }

    #[quither((!has_neither || has_either) && (!has_either || has_both))]
    pub fn right_or_insert_with<F>(&mut self, #[allow(unused)] f: F) -> &mut R
    where
        F: FnOnce() -> R,
    {
        match self {
            #[either]
            Self::Right(r) => r,
            #[either]
            Self::Left(_) => {
                // Left => Both promotion. It is guaranteed that the `Both` variant is present
                // because of the method's attribute.
                replace_with_or_abort(self, move |this| {
                    let Self::Left(l) = this else { unreachable!() };
                    Self::Both(l, f())
                });
                let Self::Both(_, r) = self else {
                    unreachable!()
                };
                r
            }
            #[neither]
            Self::Neither => {
                // Neither => Right promotion. It is guaranteed that the `Right` variant is present
                // because of the method's attribute.
                replace_with_or_abort(self, move |this| {
                    let Self::Neither = this else { unreachable!() };
                    Self::Right(f())
                });
                let Self::Right(r) = self else { unreachable!() };
                r
            }
            #[both]
            Self::Both(_, r) => r,
        }
    }

    #[quither(!has_neither || has_either)]
    pub fn ensure_left(&mut self, l: L) -> &mut L {
        self.ensure_left_with(move || l)
    }

    #[quither(!has_neither || has_either)]
    pub fn ensure_right(&mut self, r: R) -> &mut R {
        self.ensure_right_with(move || r)
    }

    /// Ensure the left value is present. If possible, keep the right value too.
    ///
    /// If the left value is already present, do nothing and return the left value.
    /// If the left value is not present, then:
    ///   - If it can "promote" the variant (`Right` => `Both`, `Neither` => `Left`), then do so.
    ///   - Otherwise, set the variant to `Left` (dispose the right value even if it is present).
    /// And set the left value to the given closure's return value and return it.
    #[quither(!has_neither || has_either)]
    pub fn ensure_left_with<F>(&mut self, #[allow(unused)] f: F) -> &mut L
    where
        F: FnOnce() -> L,
    {
        match self {
            #[either]
            Self::Left(l) => l,
            #[quither(has_either && has_both)]
            Self::Right(_) => {
                // Right => Both promotion.
                let new_l = f();
                replace_with_or_abort(self, move |this| {
                    let Self::Right(r) = this else { unreachable!() };
                    Self::Both(new_l, r)
                });
                let Self::Both(l, _) = self else {
                    unreachable!()
                };
                l
            }
            #[quither(has_either && !has_both)]
            Self::Right(_) => {
                // No promotion.
                *self = Self::Left(f());
                let Self::Left(l) = self else { unreachable!() };
                l
            }
            #[neither]
            Self::Neither => {
                // Neither => Left promotion.
                let new_l = f();
                replace_with_or_abort(self, move |this| {
                    let Self::Neither = this else { unreachable!() };
                    Self::Left(new_l)
                });
                let Self::Left(l) = self else { unreachable!() };
                l
            }
            #[both]
            Self::Both(l, _) => l,
        }
    }

    #[quither(!has_neither || has_either)]
    pub fn ensure_right_with<F>(&mut self, #[allow(unused)] f: F) -> &mut R
    where
        F: FnOnce() -> R,
    {
        match self {
            #[quither(has_either && has_both)]
            Self::Left(_) => {
                // Left => Both promotion.
                let new_r = f();
                replace_with_or_abort(self, move |this| {
                    let Self::Left(l) = this else { unreachable!() };
                    Self::Both(l, new_r)
                });
                let Self::Both(_, r) = self else {
                    unreachable!()
                };
                r
            }
            #[quither(has_either && !has_both)]
            Self::Left(_) => {
                // No promotion.
                *self = Self::Right(f());
                let Self::Right(r) = self else { unreachable!() };
                r
            }
            #[either]
            Self::Right(r) => r,
            #[neither]
            Self::Neither => {
                // Neither => Right promotion.
                let new_r = f();
                replace_with_or_abort(self, move |this| {
                    let Self::Neither = this else { unreachable!() };
                    Self::Right(new_r)
                });
                let Self::Right(r) = self else { unreachable!() };
                r
            }
            #[both]
            Self::Both(_, r) => r,
        }
    }
}
