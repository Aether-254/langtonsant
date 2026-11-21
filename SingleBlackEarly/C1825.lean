import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1825 : checkSingleBlackFast (-58, -35) 14263 .west (16, 26) (-45, 6) = true := by
  decide +kernel

end LangtonsAnt
