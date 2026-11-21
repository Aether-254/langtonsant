import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1004 : checkSingleBlackFast (-14, 8) 25300 .north (-9, 7) (-43, 11) = true := by
  decide +kernel

end LangtonsAnt
