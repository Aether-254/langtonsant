import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1345 : checkSingleBlackFast (-16, 12) 22512 .north (-6, -1) (-2, -31) = true := by
  decide +kernel

end LangtonsAnt
