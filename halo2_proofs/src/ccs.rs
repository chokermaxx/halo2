#![allow(missing_docs)]

use std::ops::Range;

use ff::Field;

use crate::circuit::Value;
use crate::plonk::{Advice, Any, Assigned, Assignment, Column, Error, Fixed, Instance, Selector};

/// Visit a circuit and keep track of cell assignment.
#[derive(Debug)]
pub struct CellDumper<F: Field> {
    pub k: u32,

    pub copy_constraints: Vec<(
        Any,   // column_type
        usize, // column_index
        usize, // row_index
        Any,   // column_type
        usize, // column_index
        usize, // row_index
    )>,
    // instance[column_index][row_index] == cell_value
    pub instance: Vec<Vec<Value<F>>>,
    // fixed[column_index][row_index] == cell_value
    pub fixed: Vec<Vec<Option<F>>>,
    // selectors[column_index][row_index] == cell_value
    pub selectors: Vec<Vec<bool>>,
    // advice[column_index][row_index] == cell_value
    pub advice: Vec<Vec<Option<F>>>,
    // A range of available rows for assignment and copies.
    pub usable_rows: Range<usize>,
}

// Based on keygen.rs.
impl<F: Field> Assignment<F> for CellDumper<F> {
    fn enter_region<NR, N>(&mut self, _: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        // Do nothing; we don't care about regions in this context.
    }

    fn exit_region(&mut self) {
        // Do nothing; we don't care about regions in this context.
    }

    fn enable_selector<A, AR>(&mut self, _: A, selector: &Selector, row: usize) -> Result<(), Error>
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        if !self.usable_rows.contains(&row) {
            return Err(Error::not_enough_rows_available(self.k));
        }

        self.selectors[selector.0][row] = true;

        Ok(())
    }

    fn query_instance(
        &self,
        column: Column<Instance>,
        row_index: usize,
    ) -> Result<Value<F>, Error> {
        if !self.usable_rows.contains(&row_index) {
            return Err(Error::not_enough_rows_available(self.k));
        }

        self.instance
            .get(column.index())
            .and_then(|column| column.get(row_index))
            .copied()
            .ok_or(Error::BoundsFailure)
    }

    fn assign_advice<V, VR, A, AR>(
        &mut self,
        _: A,
        column: Column<Advice>,
        row_index: usize,
        to: V,
    ) -> Result<(), Error>
    where
        V: FnOnce() -> Value<VR>,
        VR: Into<Assigned<F>>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        if !self.usable_rows.contains(&row_index) {
            return Err(Error::not_enough_rows_available(self.k));
        }

        *self
            .advice
            .get_mut(column.index())
            .and_then(|row| row.get_mut(row_index))
            .ok_or(Error::BoundsFailure)? = to().into_field().into_option().map(|x| x.evaluate());

        Ok(())
    }

    fn assign_fixed<V, VR, A, AR>(
        &mut self,
        _: A,
        column: Column<Fixed>,
        row_index: usize,
        to: V,
    ) -> Result<(), Error>
    where
        V: FnOnce() -> Value<VR>,
        VR: Into<Assigned<F>>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        if !self.usable_rows.contains(&row_index) {
            return Err(Error::not_enough_rows_available(self.k));
        }

        *self
            .fixed
            .get_mut(column.index())
            .and_then(|row| row.get_mut(row_index))
            .ok_or(Error::BoundsFailure)? = to().into_field().into_option().map(|x| x.evaluate());

        Ok(())
    }

    fn copy(
        &mut self,
        left_column: Column<Any>,
        left_row: usize,
        right_column: Column<Any>,
        right_row: usize,
    ) -> Result<(), Error> {
        if !self.usable_rows.contains(&left_row) || !self.usable_rows.contains(&right_row) {
            return Err(Error::not_enough_rows_available(self.k));
        }

        self.copy_constraints.push((
            *left_column.column_type(),
            left_column.index(),
            left_row,
            *right_column.column_type(),
            right_column.index(),
            right_row,
        ));

        Ok(())
    }

    fn fill_from_row(
        &mut self,
        column: Column<Fixed>,
        from_row: usize,
        to: Value<Assigned<F>>,
    ) -> Result<(), Error> {
        if !self.usable_rows.contains(&from_row) {
            return Err(Error::not_enough_rows_available(self.k));
        }

        let col = self
            .fixed
            .get_mut(column.index())
            .ok_or(Error::BoundsFailure)?;

        let filler = to.into_option().map(|x| x.evaluate());
        for row_index in self.usable_rows.clone().skip(from_row) {
            col[row_index] = filler;
        }

        Ok(())
    }

    fn push_namespace<NR, N>(&mut self, _: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        // Do nothing; we don't care about namespaces in this context.
    }

    fn pop_namespace(&mut self, _: Option<String>) {
        // Do nothing; we don't care about namespaces in this context.
    }
}

#[cfg(test)]
mod tests {
    use super::CellDumper;
    use crate::circuit::{Layouter, SimpleFloorPlanner, Value};
    use crate::plonk::{
        Advice, Any, Circuit, Column, ConstraintSystem, Error, Fixed, FloorPlanner, Instance,
        Selector,
    };
    use pasta_curves::Fp;

    #[derive(Copy, Clone)]
    struct TestConfig {
        a: Column<Fixed>,
        b: Column<Advice>,
        c: Column<Instance>,
        s: Selector,
    }

    struct TestCircuit();

    impl Circuit<Fp> for TestCircuit {
        type Config = TestConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn configure(meta: &mut ConstraintSystem<Fp>) -> Self::Config {
            let a = meta.fixed_column();
            let b = meta.advice_column();
            let c = meta.instance_column();
            let s = meta.selector();

            Self::Config { a, b, c, s }
        }

        fn without_witnesses(&self) -> Self {
            Self()
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fp>,
        ) -> Result<(), Error> {
            layouter.assign_region(
                || "region",
                |mut region| {
                    // to test assignment extractions

                    config.s.enable(&mut region, 0)?;
                    region.assign_fixed(|| "", config.a, 0, || Value::known(Fp::from(123)))?;
                    region.assign_advice(|| "", config.b, 0, || Value::known(Fp::from(321)))?;

                    region.assign_fixed(|| "", config.a, 1, || Value::known(Fp::from(456)))?;
                    region.assign_advice(|| "", config.b, 1, || Value::known(Fp::from(654)))?;

                    config.s.enable(&mut region, 2)?;
                    region.assign_fixed(|| "", config.a, 2, || Value::known(Fp::from(789)))?;
                    region.assign_advice(|| "", config.b, 2, || Value::known(Fp::from(987)))?;

                    // to test copy constraint extractions

                    let above =
                        region.assign_advice(|| "", config.b, 3, || Value::known(Fp::from(111)))?;
                    let below =
                        region.assign_advice(|| "", config.b, 4, || Value::known(Fp::from(111)))?;
                    region.constrain_equal(above.cell(), below.cell())?;

                    let left =
                        region.assign_fixed(|| "", config.a, 3, || Value::known(Fp::from(111)))?;
                    region.constrain_equal(left.cell(), above.cell())?;

                    // to test query_instance
                    region.assign_advice_from_instance(|| "", config.c, 0, config.b, 5)?;

                    Ok(())
                },
            )?;

            Ok(())
        }
    }

    #[test]
    fn dump_cells() -> Result<(), Error> {
        let k = 5;
        let n = 1usize << k;
        let mut meta = ConstraintSystem::default();
        let config = TestCircuit::configure(&mut meta);

        let mut instance = vec![vec![Value::unknown(); n]; meta.num_instance_columns];
        instance[0][0] = Value::known(Fp::from(777));

        let mut cell_dumper: CellDumper<Fp> = CellDumper {
            k,
            instance,
            fixed: vec![vec![None; n]; meta.num_fixed_columns],
            advice: vec![vec![None; n]; meta.num_advice_columns],
            selectors: vec![vec![false; n]; meta.num_selectors],
            copy_constraints: Vec::new(),
            usable_rows: 0..(n - meta.blinding_factors() - 1), // Why -1?
        };

        let circuit = TestCircuit();
        <<TestCircuit as Circuit<Fp>>::FloorPlanner as FloorPlanner>::synthesize(
            &mut cell_dumper,
            &circuit,
            config,
            meta.constants.clone(),
        )?;

        assert!(cell_dumper.selectors[0][0]);
        assert_eq!(cell_dumper.fixed[0][0], Some(Fp::from(123)));
        assert_eq!(cell_dumper.advice[0][0], Some(Fp::from(321)));

        assert!(!cell_dumper.selectors[0][1]);
        assert_eq!(cell_dumper.fixed[0][1], Some(Fp::from(456)));
        assert_eq!(cell_dumper.advice[0][1], Some(Fp::from(654)));

        assert!(cell_dumper.selectors[0][2]);
        assert_eq!(cell_dumper.fixed[0][2], Some(Fp::from(789)));
        assert_eq!(cell_dumper.advice[0][2], Some(Fp::from(987)));

        assert_eq!(
            cell_dumper.copy_constraints[0],
            (Any::Advice, 0, 3, Any::Advice, 0, 4)
        );
        assert_eq!(
            cell_dumper.copy_constraints[1],
            (Any::Fixed, 0, 3, Any::Advice, 0, 3)
        );

        assert_eq!(cell_dumper.advice[0][5], Some(Fp::from(777)));

        Ok(())
    }
}
