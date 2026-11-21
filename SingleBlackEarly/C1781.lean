import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1781 : checkSingleBlackFast (-54, -31) 14055 .west (14, 24) (-43, 4) = true := by
  decide +kernel

end LangtonsAnt
