From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
From CraneTestsRegression.sep_ext_modname_clash.Bar Require Import Foo.
From CraneTestsRegression.sep_ext_modname_clash.Baz Require Import Foo.

Crane Separate Extraction bar_add bar_only baz_add baz_only.
