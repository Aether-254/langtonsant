import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1440 : checkSingleBlackFast (-20, 0) 29552 .north (-2, 0) (-4, -36) = true := by
  decide +kernel

end LangtonsAnt
