import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1387 : checkSingleBlackFast (-18, 4) 24388 .north (-6, -1) (-6, -35) = true := by
  decide +kernel

end LangtonsAnt
