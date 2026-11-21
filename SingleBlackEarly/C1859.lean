import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1859 : checkSingleBlackFast (-57, -39) 12424 .north (18, 10) (-44, -26) = true := by
  decide +kernel

end LangtonsAnt
