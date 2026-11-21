import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2107 : checkSingleBlackFast (-85, -57) 26049 .east (38, 26) (16, -61) = true := by
  decide +kernel

end LangtonsAnt
