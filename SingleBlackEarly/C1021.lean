import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1021 : checkSingleBlackFast (-6, 19) 21556 .north (-6, 0) (0, -28) = true := by
  decide +kernel

end LangtonsAnt
