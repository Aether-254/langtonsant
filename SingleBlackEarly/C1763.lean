import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1763 : checkSingleBlackFast (-53, -29) 14055 .west (13, 24) (-43, 5) = true := by
  decide +kernel

end LangtonsAnt
