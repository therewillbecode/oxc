import { AExtend, BExtend, Type, CImplements1, CImplements2, CType, ThisType1, ThisType2, ThisType3, Unused, fn } from 'mod';

export interface A extends AExtend<Type> {}
export class B extends BExtend<Type> {}
export class C implements CImplements1<CType>, CImplements2<CType> {}
export class D { method(this: ThisType1): void { } }
export function foo(this: ThisType2): void {}
export const bar: (this: ThisType3) => void = function() {}

import { type InferType1, type InferType2 } from 'infer';

export type F<X extends InferType1> = X extends infer U extends InferType2 ? U : never
export interface VitestUtils {
  fn: typeof fn;
  isMockFunction: (fn: any) => fn is any;
}

export { Unused } from './unused';