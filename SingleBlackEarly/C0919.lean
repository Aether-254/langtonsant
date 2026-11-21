import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0919 : checkSingleBlackFast (-6, 13) 8843 .east (0, -6) (-21, -20) = true := by
  decide +kernel

end LangtonsAnt
