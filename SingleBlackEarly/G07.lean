import FastCell2
import SingleBlackEarly.C0259
import SingleBlackEarly.C0260
import SingleBlackEarly.C0261
import SingleBlackEarly.C0262
import SingleBlackEarly.C0263
import SingleBlackEarly.C0264
import SingleBlackEarly.C0265
import SingleBlackEarly.C0266
import SingleBlackEarly.C0267
import SingleBlackEarly.C0268
import SingleBlackEarly.C0269
import SingleBlackEarly.C0270
import SingleBlackEarly.C0271
import SingleBlackEarly.C0272
import SingleBlackEarly.C0273
import SingleBlackEarly.C0274
import SingleBlackEarly.C0275
import SingleBlackEarly.C0276
import SingleBlackEarly.C0277
import SingleBlackEarly.C0278
import SingleBlackEarly.C0279
import SingleBlackEarly.C0280
import SingleBlackEarly.C0281
import SingleBlackEarly.C0282
import SingleBlackEarly.C0283
import SingleBlackEarly.C0284
import SingleBlackEarly.C0285
import SingleBlackEarly.C0286
import SingleBlackEarly.C0287
import SingleBlackEarly.C0288
import SingleBlackEarly.C0289
import SingleBlackEarly.C0290
import SingleBlackEarly.C0291
import SingleBlackEarly.C0292
import SingleBlackEarly.C0293
import SingleBlackEarly.C0294
import SingleBlackEarly.C0295

namespace LangtonsAnt

def sbGroup07 : List Point :=
  [(11, 11), (12, 11), (10, 11), (10, 12), (11, 12), (10, 10), (13, 8), (13, 7), (12, 7), (14, 7), (14, 6), (14, 5), (14, 4), (13, 4), (14, 8), (15, 8), (15, 7), (15, 9), (16, 9), (16, 8), (14, 9), (14, 10), (15, 10), (15, 11), (16, 11), (16, 10), (14, 11), (14, 12), (15, 12), (13, 12), (13, 13), (14, 13), (13, 11), (12, 12), (9, 12), (9, 13), (10, 13)]

theorem sbGroup07_ok : forall q, q ∈ sbGroup07 -> EventuallyStandard (singleBlack q) := by
  intro q hq
  simp only [sbGroup07, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSingleBlackFast_sound sbCell0259
  · exact checkSingleBlackFast_sound sbCell0260
  · exact checkSingleBlackFast_sound sbCell0261
  · exact checkSingleBlackFast_sound sbCell0262
  · exact checkSingleBlackFast_sound sbCell0263
  · exact checkSingleBlackFast_sound sbCell0264
  · exact checkSingleBlackFast2_sound sbCell0265
  · exact checkSingleBlackFast_sound sbCell0266
  · exact checkSingleBlackFast_sound sbCell0267
  · exact checkSingleBlack_sound sbCell0268
  · exact checkSingleBlackFast_sound sbCell0269
  · exact checkSingleBlackFast2_sound sbCell0270
  · exact checkSingleBlackFast_sound sbCell0271
  · exact checkSingleBlackFast_sound sbCell0272
  · exact checkSingleBlackFast_sound sbCell0273
  · exact checkSingleBlackFast_sound sbCell0274
  · exact checkSingleBlackFast_sound sbCell0275
  · exact checkSingleBlackFast2_sound sbCell0276
  · exact checkSingleBlackFast_sound sbCell0277
  · exact checkSingleBlackFast_sound sbCell0278
  · exact checkSingleBlackFast_sound sbCell0279
  · exact checkSingleBlackFast2_sound sbCell0280
  · exact checkSingleBlackFast_sound sbCell0281
  · exact checkSingleBlackFast_sound sbCell0282
  · exact checkSingleBlackFast_sound sbCell0283
  · exact checkSingleBlackFast_sound sbCell0284
  · exact checkSingleBlackFast_sound sbCell0285
  · exact checkSingleBlack_sound sbCell0286
  · exact checkSingleBlackFast_sound sbCell0287
  · exact checkSingleBlackFast_sound sbCell0288
  · exact checkSingleBlackFast_sound sbCell0289
  · exact checkSingleBlack_sound sbCell0290
  · exact checkSingleBlackFast_sound sbCell0291
  · exact checkSingleBlackFast_sound sbCell0292
  · exact checkSingleBlackFast_sound sbCell0293
  · exact checkSingleBlackFast_sound sbCell0294
  · exact checkSingleBlackFast_sound sbCell0295

end LangtonsAnt
